import GaloisForLFunctions.FamilyContinuationTheory.TheCorrectionOfThePrincipalRowIsAConvergentEulerProduct

/-!
# The wall of the frame is a phase `L`-function

The correction of the target in the two-estimate frame is the Euler product of the local factors
`h(s) = (1 − Q⁻²)(1 − Q⁻¹(R − D)/(1 − D))/(1 − R)`, `R = A Q^{3−6s}`, `D = η Q^{−s}`
(`principalLocalFactor`). Its denominator is the local factor of the **phase `L`-function**
`L_A(w) = Π (1 − A_v N(v)^{−w})⁻¹` at `w = 6s − 3`; the numerator is within `9 Q^{−e}` of one for
`e ≤ min(6σ − 2, 1 + σ, 2)`, which exceeds one on all of `Re s > ½`.

* `principalCorrection_eq_phaseLFunction_mul`: on `Re s > 2/3`, `H(s) = L_A(6s − 3) E(s)`, with
  `E` holomorphic and within `½` of one on every half-plane `Re s > σ > ½`
  (`exists_regularCorrection_cutoff`).
* `framePremise_iff`: for `½ < σ`, the correction continues holomorphically and without zeros to
  `Re s > σ` exactly when the phase `L`-function continues holomorphically and without zeros to
  `Re w > 6σ − 3`. The nonvanishing premise of the frame below `2/3` is a zero-free half-plane of
  `L_A`; for the probe `A_v = κ_v⁶` is a Hecke character of infinite order times `η⁶`, so the wall
  of the frame sits at `(3 + Θ_A)/6`, `Θ_A` the zero abscissa of `L_A`.
* `heckeLFunction_transport`: the two estimates with a correction that is only holomorphic give,
  right of the comparison exponents, that every zero of `L(s, η)` is a zero of the correction.
  Below the wall the frame is a transport law: a zero `ρ` of `L(s, η)` forces a zero `6ρ − 3` of
  the phase `L`-function (`heckeLFunction_transport_phase`).
-/

noncomputable section

open Complex NumberField IsDedekindDomain

namespace GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies

open FamilyContinuationTheory HeckeLFunctions

/-! ### The local factors -/

/-- The denominator `1 − A Q^{3−6s}` of the principal local factor. -/
def wallLocalFactor (Q : ℝ) (A s : ℂ) : ℂ := 1 - A * (Q : ℂ) ^ (3 - 6 * s)

/-- The numerator `(1 − Q⁻²)(1 − Q⁻¹(R − D)/(1 − D))` of the principal local factor. -/
def regularLocalFactor (Q : ℝ) (A η s : ℂ) : ℂ :=
  (1 - ((Q : ℂ)⁻¹) ^ 2) *
    (1 - (Q : ℂ)⁻¹ * (A * (Q : ℂ) ^ (3 - 6 * s) - η * (Q : ℂ) ^ (-s)) /
      (1 - η * (Q : ℂ) ^ (-s)))

/-- The local factor `(1 − A Q^{−w})⁻¹` of the phase `L`-function. -/
def phaseLocalFactor (Q : ℝ) (A w : ℂ) : ℂ := (1 - A * (Q : ℂ) ^ (-w))⁻¹

theorem principalLocalFactor_eq_phase_mul (Q : ℝ) (A η s : ℂ) :
    principalLocalFactor Q A η s =
      phaseLocalFactor Q A (6 * s - 3) * regularLocalFactor Q A η s := by
  unfold principalLocalFactor phaseLocalFactor regularLocalFactor
  rw [neg_sub, div_eq_inv_mul]

/-- **The regular part is close to one on `Re s > ½`.** For `Q ≥ 4`, `‖A‖, ‖η‖ ≤ 1` and
`½ ≤ σ ≤ Re s`, `‖E_loc − 1‖ ≤ 9 Q^{−e}` whenever `e ≤ min(6σ − 2, 1 + σ, 2)`. -/
theorem norm_regularLocalFactor_sub_one_le {Q σ e : ℝ} {A η s : ℂ} (hQ : 4 ≤ Q)
    (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hσ : 1 / 2 ≤ σ) (hs : σ ≤ s.re) (he6 : e ≤ 6 * σ - 2)
    (heσ : e ≤ 1 + σ) (he2 : e ≤ 2) :
    ‖regularLocalFactor Q A η s - 1‖ ≤ 9 * Q ^ (-e) := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  set D := η * (Q : ℂ) ^ (-s) with hDdef
  set R := A * (Q : ℂ) ^ (3 - 6 * s) with hRdef
  set q : ℂ := (Q : ℂ)⁻¹ with hqdef
  set T := Q ^ (-e) with hTdef
  have hT0 : 0 ≤ T := Real.rpow_nonneg hQ0.le _
  have hq : ‖q‖ = Q ^ (-1 : ℝ) := by
    rw [hqdef, norm_inv, Complex.norm_real, Real.norm_of_nonneg hQ0.le, Real.rpow_neg_one]
  have hD : ‖D‖ ≤ Q ^ (-σ) := by
    rw [hDdef, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hη).trans
      (norm_ofReal_cpow_le hQ1 (by rw [neg_re]; linarith))
  have hR : ‖R‖ ≤ Q ^ (3 - 6 * σ) := by
    rw [hRdef, norm_mul]
    refine (mul_le_of_le_one_left (norm_nonneg _) hA).trans (norm_ofReal_cpow_le hQ1 ?_)
    simp only [sub_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]
    linarith
  have hDh : ‖D‖ ≤ 1 / 2 := hD.trans (rpow_le_half_of_four_le hQ (by linarith))
  have hqR : ‖q‖ * ‖R‖ ≤ T := by
    rw [hq]
    calc Q ^ (-1 : ℝ) * ‖R‖ ≤ Q ^ (-1 : ℝ) * Q ^ (3 - 6 * σ) :=
          mul_le_mul_of_nonneg_left hR (Real.rpow_nonneg hQ0.le _)
      _ = Q ^ (-1 + (3 - 6 * σ)) := (Real.rpow_add hQ0 _ _).symm
      _ ≤ T := Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have hqD : ‖q‖ * ‖D‖ ≤ T := by
    rw [hq]
    calc Q ^ (-1 : ℝ) * ‖D‖ ≤ Q ^ (-1 : ℝ) * Q ^ (-σ) :=
          mul_le_mul_of_nonneg_left hD (Real.rpow_nonneg hQ0.le _)
      _ = Q ^ (-1 + -σ) := (Real.rpow_add hQ0 _ _).symm
      _ ≤ T := Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have hq2 : ‖q‖ ^ 2 ≤ T := by
    rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul hQ0.le]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num; linarith)
  have hq2' : ‖q‖ ^ 2 ≤ 1 := by
    rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul hQ0.le]
    exact Real.rpow_le_one_of_one_le_of_nonpos hQ1 (by norm_num)
  have h1D : 1 / 2 ≤ ‖1 - D‖ := by
    have := norm_sub_norm_le (1 : ℂ) D
    rw [norm_one] at this
    linarith
  have ha : ‖q * (R - D) / (1 - D)‖ ≤ 4 * T := by
    rw [norm_div, norm_mul, div_le_iff₀ (by linarith)]
    calc ‖q‖ * ‖R - D‖ ≤ ‖q‖ * (‖R‖ + ‖D‖) :=
          mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
      _ = ‖q‖ * ‖R‖ + ‖q‖ * ‖D‖ := by ring
      _ ≤ T + T := add_le_add hqR hqD
      _ ≤ 4 * T * ‖1 - D‖ := by nlinarith
  have hrw : regularLocalFactor Q A η s - 1 =
      -(q ^ 2) - q * (R - D) / (1 - D) * (1 - q ^ 2) := by
    unfold regularLocalFactor
    ring
  have h1q : ‖1 - q ^ 2‖ ≤ 2 := by
    have h := norm_sub_le (1 : ℂ) (q ^ 2)
    rw [norm_one, norm_pow] at h
    linarith
  rw [hrw]
  calc ‖-(q ^ 2) - q * (R - D) / (1 - D) * (1 - q ^ 2)‖
      ≤ ‖q ^ 2‖ + ‖q * (R - D) / (1 - D) * (1 - q ^ 2)‖ := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_neg]
    _ ≤ T + 4 * T * 2 := by
        rw [norm_pow, norm_mul]
        exact add_le_add hq2 (mul_le_mul ha h1q (norm_nonneg _) (by positivity))
    _ = 9 * T := by ring

/-- **The phase factor is close to one on `Re w ≥ τ ≥ 1`.** -/
theorem norm_phaseLocalFactor_sub_one_le {Q τ : ℝ} {A w : ℂ} (hQ : 2 ≤ Q) (hA : ‖A‖ ≤ 1)
    (hτ : 1 ≤ τ) (hw : τ ≤ w.re) : ‖phaseLocalFactor Q A w - 1‖ ≤ 2 * Q ^ (-τ) := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  set a := A * (Q : ℂ) ^ (-w) with hadef
  have ha : ‖a‖ ≤ Q ^ (-τ) := by
    rw [hadef, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hA).trans
      (norm_ofReal_cpow_le hQ1 (by rw [neg_re]; linarith))
  have hQτ : Q ^ (-τ) ≤ 1 / 2 := by
    calc Q ^ (-τ) ≤ Q ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
      _ = Q⁻¹ := Real.rpow_neg_one Q
      _ ≤ 1 / 2 := by rw [inv_eq_one_div]; exact div_le_div_of_nonneg_left (by norm_num)
                        (by norm_num) hQ
  have h1a : 1 / 2 ≤ ‖1 - a‖ := by
    have := norm_sub_norm_le (1 : ℂ) a
    rw [norm_one] at this
    linarith
  have hne : 1 - a ≠ 0 := norm_pos_iff.mp (by linarith)
  have hrw : phaseLocalFactor Q A w - 1 = a / (1 - a) := by
    unfold phaseLocalFactor
    rw [← hadef]
    field_simp
    ring
  rw [hrw, norm_div, div_le_iff₀ (by linarith)]
  nlinarith [norm_nonneg a]

/-- The regular factor is holomorphic where `1 − η Q^{−s} ≠ 0`. -/
theorem differentiableAt_regularLocalFactor {Q : ℝ} (hQ : 0 < Q) (A η : ℂ) {s : ℂ}
    (hD : 1 - η * (Q : ℂ) ^ (-s) ≠ 0) :
    DifferentiableAt ℂ (regularLocalFactor Q A η) s := by
  have hQ' : (Q : ℂ) ≠ 0 := ofReal_ne_zero.mpr hQ.ne'
  have h1 : DifferentiableAt ℂ (fun s : ℂ => (Q : ℂ) ^ (-s)) s :=
    differentiableAt_id.neg.const_cpow (Or.inl hQ')
  have h2 : DifferentiableAt ℂ (fun s : ℂ => (Q : ℂ) ^ (3 - 6 * s)) s :=
    ((differentiableAt_const 3).sub ((differentiableAt_const 6).mul differentiableAt_id)).const_cpow
      (Or.inl hQ')
  exact (differentiableAt_const _).mul ((differentiableAt_const 1).sub
    (((differentiableAt_const _).mul ((h2.const_mul A).sub (h1.const_mul η))).div
      ((differentiableAt_const 1).sub (h1.const_mul η)) hD))

/-- The denominator `1 − η Q^{−s}` does not vanish for `Q ≥ 4`, `Re s ≥ ½`. -/
theorem regular_denominator_ne_zero {Q : ℝ} (hQ : 4 ≤ Q) {η s : ℂ} (hη : ‖η‖ ≤ 1)
    (hs : 1 / 2 ≤ s.re) : 1 - η * (Q : ℂ) ^ (-s) ≠ 0 := by
  have hQ1 : 1 ≤ Q := by linarith
  have hD : ‖η * (Q : ℂ) ^ (-s)‖ ≤ 1 / 2 := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hη).trans
      ((norm_ofReal_cpow_le hQ1 (a := -(1 / 2)) (by rw [neg_re]; linarith)).trans
        (rpow_le_half_of_four_le hQ le_rfl))
  intro h
  have := norm_sub_norm_le (1 : ℂ) (η * (Q : ℂ) ^ (-s))
  rw [h, norm_zero, norm_one] at this
  linarith

/-- The phase factor is holomorphic on `Re w > 0` for `Q ≥ 2`, `‖A‖ ≤ 1`. -/
theorem differentiableAt_phaseLocalFactor {Q : ℝ} (hQ : 2 ≤ Q) {A : ℂ} (hA : ‖A‖ ≤ 1)
    {w : ℂ} (hw : 0 < w.re) : DifferentiableAt ℂ (phaseLocalFactor Q A) w := by
  have hQ0 : 0 < Q := by linarith
  have hQ' : (Q : ℂ) ≠ 0 := ofReal_ne_zero.mpr hQ0.ne'
  have hlt : ‖A * (Q : ℂ) ^ (-w)‖ < 1 := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hQ0, neg_re]
    calc ‖A‖ * Q ^ (-w.re) ≤ 1 * Q ^ (-w.re) :=
          mul_le_mul_of_nonneg_right hA (Real.rpow_nonneg hQ0.le _)
      _ < 1 := by rw [one_mul]; exact Real.rpow_lt_one_of_one_lt_of_neg (by linarith)
                    (by linarith)
  have hne : 1 - A * (Q : ℂ) ^ (-w) ≠ 0 := by
    intro h
    have := norm_sub_norm_le (1 : ℂ) (A * (Q : ℂ) ^ (-w))
    rw [h, norm_zero, norm_one] at this
    linarith
  exact ((differentiableAt_const 1).sub
    ((differentiableAt_id.neg.const_cpow (Or.inl hQ')).const_mul A)).inv hne

/-! ### Products over the primes of a number field -/

section NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- The regular part of the correction. -/
def regularCorrection (A η : HeightOneSpectrum (𝓞 K) → ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (s : ℂ) : ℂ :=
  ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}, regularLocalFactor (primeNorm v.1) (A v.1) (η v.1) s

/-- The phase `L`-function `Π_{v ∉ S} (1 − A_v N(v)^{−w})⁻¹`. -/
def phaseLFunction (A : HeightOneSpectrum (𝓞 K) → ℂ) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (w : ℂ) : ℂ :=
  ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}, phaseLocalFactor (primeNorm v.1) (A v.1) w

/-- **Products with a summable power majorant.** For `e > 1` and `C ≥ 0` there is a norm `N₀`
such that, whenever `S` contains every prime of norm `≤ N₀`, every family of factors holomorphic
on an open `U` with `‖f_v − 1‖ ≤ C N(v)^{−e}` at the primes of norm `≥ 4` has a holomorphic
product on `U` within `½` of one. -/
theorem exists_cutoff_product {e C : ℝ} (he : 1 < e) (hC : 0 ≤ C) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ (S : Finset (HeightOneSpectrum (𝓞 K))),
      (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal.absNorm ≤ N₀ → v ∈ S) →
      ∀ (U : Set ℂ), IsOpen U → ∀ f : HeightOneSpectrum (𝓞 K) → ℂ → ℂ,
        (∀ v, 4 ≤ primeNorm v → DifferentiableOn ℂ (f v) U) →
        (∀ v, 4 ≤ primeNorm v → ∀ s ∈ U, ‖f v s - 1‖ ≤ C * primeNorm v ^ (-e)) →
        DifferentiableOn ℂ (fun s => ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}, f v.1 s) U ∧
          ∀ s ∈ U, ‖(∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}, f v.1 s) - 1‖ ≤ 1 / 2 := by
  set b : HeightOneSpectrum (𝓞 K) → ℝ := fun v => C * primeNorm v ^ (-e) with hbdef
  have hb0 : ∀ v, 0 ≤ b v := fun v => mul_nonneg hC (Real.rpow_nonneg (by positivity) _)
  have hB : Summable b := (numberField_summable_finitePlace_absNorm_rpow (K := K) he).mul_left C
  obtain ⟨F, hF⟩ := ((tendsto_order.1 (tendsto_tsum_compl_atTop_zero b)).2 (1 / 6)
    (by norm_num)).exists
  refine ⟨max 4 (F.sup fun v => v.asIdeal.absNorm), le_max_left _ _, ?_⟩
  intro S hS U hU f hf hfb
  have hbig : ∀ v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}, 4 ≤ primeNorm v.1 ∧ v.1 ∉ F := by
    intro v
    have hv : max 4 (F.sup fun v => v.asIdeal.absNorm) < v.1.asIdeal.absNorm :=
      lt_of_not_ge fun h => v.2 (hS v.1 h)
    refine ⟨?_, fun hF' => ?_⟩
    · have : 4 < v.1.asIdeal.absNorm := (le_max_left _ _).trans_lt hv
      unfold primeNorm
      exact_mod_cast this.le
    · exact absurd ((Finset.le_sup (f := fun v => v.asIdeal.absNorm) hF').trans
        (le_max_right _ _)) (not_le.mpr hv)
  have hBT : Summable fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} => b v.1 :=
    hB.comp_injective Subtype.val_injective
  have hsmall : ∑' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}, b v.1 ≤ 1 / 6 := by
    have hi : Function.Injective fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
        (⟨v.1, (hbig v).2⟩ : {v // v ∉ F}) := fun v w h =>
      Subtype.ext (congrArg (fun x : {v // v ∉ F} => x.1) h)
    have hBF : Summable fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ F} => b v.1 :=
      hB.comp_injective Subtype.val_injective
    have h1 : ∑' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}, b v.1 ≤
        ∑' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ F}, b v.1 :=
      Summable.tsum_le_tsum_of_inj (f := fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} => b v.1)
        (g := fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ F} => b v.1)
        _ hi (fun _ _ => hb0 _) (fun _ => le_rfl) hBT hBF
    exact h1.trans hF.le
  have hhalf : ∀ v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}, b v.1 ≤ 1 / 2 := fun v => by
    have := Summable.le_tsum hBT v fun w _ => hb0 w.1
    linarith
  obtain ⟨hdiff, hrep⟩ := hasProd_and_bounds_of_defect
    (f := fun (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) s => f v.1 s)
    (b := fun v => b v.1) hU hBT (fun v => hf v.1 (hbig v).1)
    (fun v s hs => hfb v.1 (hbig v).1 s hs) hhalf
  refine ⟨hdiff, fun s hs => ?_⟩
  obtain ⟨hexp, hlog⟩ := hrep s hs
  have hz : ‖∑' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}, Complex.log (f v.1 s)‖ ≤ 1 / 4 :=
    hlog.trans (by linarith)
  rw [hexp]
  calc _ ≤ 2 * ‖∑' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}, Complex.log (f v.1 s)‖ :=
        Complex.norm_exp_sub_one_le (hz.trans (by norm_num))
    _ ≤ 1 / 2 := by linarith

/-- The exponent `min(6σ − 2, 1 + σ, 2)` of the regular part; it exceeds `1` for `σ > ½`. -/
def regularExponent (σ : ℝ) : ℝ := min (6 * σ - 2) (min (1 + σ) 2)

theorem one_lt_regularExponent {σ : ℝ} (hσ : 1 / 2 < σ) : 1 < regularExponent σ :=
  lt_min (by linarith) (lt_min (by linarith) (by norm_num))

/-- **The regular part converges on `Re s > ½`.** For `σ > ½` there is a norm `N₀` such that,
whenever `S` contains every prime of norm `≤ N₀`, the regular part with any phases of modulus
`≤ 1` is holomorphic on `Re s > σ` and within `½` of one there; in particular it has no zero. -/
theorem exists_regularCorrection_cutoff {σ : ℝ} (hσ : 1 / 2 < σ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ (S : Finset (HeightOneSpectrum (𝓞 K))),
      (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal.absNorm ≤ N₀ → v ∈ S) →
      ∀ A η : HeightOneSpectrum (𝓞 K) → ℂ, (∀ v, ‖A v‖ ≤ 1) → (∀ v, ‖η v‖ ≤ 1) →
        DifferentiableOn ℂ (regularCorrection A η S) {s : ℂ | σ < s.re} ∧
          ∀ s : ℂ, σ < s.re → ‖regularCorrection A η S s - 1‖ ≤ 1 / 2 := by
  obtain ⟨N₀, hN₀, hcut⟩ := exists_cutoff_product (K := K) (one_lt_regularExponent hσ)
    (by norm_num : (0 : ℝ) ≤ 9)
  refine ⟨N₀, hN₀, fun S hS A η hA hη => ?_⟩
  have hU : IsOpen {s : ℂ | σ < s.re} := isOpen_lt continuous_const continuous_re
  have he6 : regularExponent σ ≤ 6 * σ - 2 := min_le_left _ _
  have heσ : regularExponent σ ≤ 1 + σ := (min_le_right _ _).trans (min_le_left _ _)
  have he2 : regularExponent σ ≤ 2 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨h1, h2⟩ := hcut S hS {s : ℂ | σ < s.re} hU
    (fun v s => regularLocalFactor (primeNorm v) (A v) (η v) s)
    (fun v hv s hs => (differentiableAt_regularLocalFactor (by linarith) _ _
      (regular_denominator_ne_zero hv (hη v) (by
        have : σ < s.re := hs
        linarith))).differentiableWithinAt)
    (fun v hv s hs => norm_regularLocalFactor_sub_one_le hv (hA v) (hη v) hσ.le (le_of_lt hs)
      he6 heσ he2)
  exact ⟨h1, fun s hs => h2 s hs⟩

/-- **The phase `L`-function converges on `Re w > 1`.** For `τ > 1` there is a norm `N₀` such
that, whenever `S` contains every prime of norm `≤ N₀`, `L_A` is holomorphic on `Re w > τ` and
within `½` of one there, for all phases of modulus `≤ 1`. -/
theorem exists_phaseLFunction_cutoff {τ : ℝ} (hτ : 1 < τ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ (S : Finset (HeightOneSpectrum (𝓞 K))),
      (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal.absNorm ≤ N₀ → v ∈ S) →
      ∀ A : HeightOneSpectrum (𝓞 K) → ℂ, (∀ v, ‖A v‖ ≤ 1) →
        DifferentiableOn ℂ (phaseLFunction A S) {w : ℂ | τ < w.re} ∧
          ∀ w : ℂ, τ < w.re → ‖phaseLFunction A S w - 1‖ ≤ 1 / 2 := by
  obtain ⟨N₀, hN₀, hcut⟩ := exists_cutoff_product (K := K) hτ (by norm_num : (0 : ℝ) ≤ 2)
  refine ⟨N₀, hN₀, fun S hS A hA => ?_⟩
  have hU : IsOpen {w : ℂ | τ < w.re} := isOpen_lt continuous_const continuous_re
  obtain ⟨h1, h2⟩ := hcut S hS {w : ℂ | τ < w.re} hU
    (fun v w => phaseLocalFactor (primeNorm v) (A v) w)
    (fun v hv w hw => (differentiableAt_phaseLocalFactor (by linarith) (hA v) (by
        have : τ < w.re := hw
        linarith)).differentiableWithinAt)
    (fun v hv w hw => norm_phaseLocalFactor_sub_one_le (by linarith) (hA v) hτ.le (le_of_lt hw))
  exact ⟨h1, fun w hw => h2 w hw⟩

/-- **The correction factors through the phase `L`-function.** If `S` contains every prime of
norm `≤ 4`, then on `Re s > 2/3`, `H(s) = L_A(6s − 3) E(s)`. -/
theorem principalCorrection_eq_phaseLFunction_mul (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal.absNorm ≤ 4 → v ∈ S)
    (A η : HeightOneSpectrum (𝓞 K) → ℂ) (hA : ∀ v, ‖A v‖ ≤ 1) (hη : ∀ v, ‖η v‖ ≤ 1) {s : ℂ}
    (hs : 2 / 3 < s.re) :
    principalCorrection A η S s = phaseLFunction A S (6 * s - 3) * regularCorrection A η S s := by
  have hbig : ∀ v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}, 4 ≤ primeNorm v.1 := by
    intro v
    have hv : 4 < v.1.asIdeal.absNorm := lt_of_not_ge fun h => v.2 (hS v.1 h)
    unfold primeNorm
    exact_mod_cast hv.le
  have hτ : 1 < (6 * s - 3).re := by
    simp only [sub_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]
    linarith
  have hσ : 1 / 2 < s.re := by linarith
  -- both families of local factors have summable defects
  have hsum1 : Summable fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
      phaseLocalFactor (primeNorm v.1) (A v.1) (6 * s - 3) - 1 := by
    refine Summable.of_norm_bounded
      (((numberField_summable_finitePlace_absNorm_rpow (K := K) hτ).mul_left 2).comp_injective
        Subtype.val_injective) fun v => ?_
    exact norm_phaseLocalFactor_sub_one_le (by linarith [hbig v]) (hA v.1) hτ.le le_rfl
  have hsum2 : Summable fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
      regularLocalFactor (primeNorm v.1) (A v.1) (η v.1) s - 1 := by
    refine Summable.of_norm_bounded
      (((numberField_summable_finitePlace_absNorm_rpow (K := K)
        (one_lt_regularExponent hσ)).mul_left 9).comp_injective Subtype.val_injective) fun v => ?_
    exact norm_regularLocalFactor_sub_one_le (hbig v) (hA v.1) (η := η v.1) (hη v.1) hσ.le le_rfl
      (min_le_left _ _) ((min_le_right _ _).trans (min_le_left _ _))
      ((min_le_right _ _).trans (min_le_right _ _))
  have hm1 := Complex.multipliable_one_add_of_summable hsum1
  have hm2 := Complex.multipliable_one_add_of_summable hsum2
  simp only [add_sub_cancel] at hm1 hm2
  unfold principalCorrection phaseLFunction regularCorrection
  simp_rw [principalLocalFactor_eq_phase_mul]
  exact hm1.tprod_mul hm2

/-- **The frame premise below the wall is a zero-free half-plane of the phase `L`-function.**
For `σ > ½` there is a norm `N₀` such that, whenever `S` contains every prime of norm `≤ N₀`: the
correction has a holomorphic continuation to `Re s > σ` without zeros if and only if the phase
`L`-function has a holomorphic continuation to `Re w > 6σ − 3` without zeros. -/
theorem framePremise_iff {σ : ℝ} (hσ : 1 / 2 < σ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ (S : Finset (HeightOneSpectrum (𝓞 K))),
      (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal.absNorm ≤ N₀ → v ∈ S) →
      ∀ A η : HeightOneSpectrum (𝓞 K) → ℂ, (∀ v, ‖A v‖ ≤ 1) → (∀ v, ‖η v‖ ≤ 1) →
        ((∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s : ℂ | σ < s.re} ∧
            (∀ s : ℂ, 2 / 3 < s.re → G s = principalCorrection A η S s) ∧
            ∀ s : ℂ, σ < s.re → G s ≠ 0) ↔
          (∃ Λ : ℂ → ℂ, DifferentiableOn ℂ Λ {w : ℂ | 6 * σ - 3 < w.re} ∧
            (∀ w : ℂ, 1 < w.re → Λ w = phaseLFunction A S w) ∧
            ∀ w : ℂ, 6 * σ - 3 < w.re → Λ w ≠ 0)) := by
  obtain ⟨N₀, hN₀, hcut⟩ := exists_regularCorrection_cutoff (K := K) hσ
  refine ⟨N₀, hN₀, fun S hS A η hA hη => ?_⟩
  obtain ⟨hEd, hEb⟩ := hcut S hS A η hA hη
  have hS4 : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal.absNorm ≤ 4 → v ∈ S :=
    fun v hv => hS v (hv.trans hN₀)
  set E := regularCorrection A η S with hEdef
  have hE0 : ∀ s : ℂ, σ < s.re → E s ≠ 0 := by
    intro s hs h0
    have := hEb s hs
    rw [h0, zero_sub, norm_neg, norm_one] at this
    linarith
  -- the affine change of variable `w = 6s − 3`
  have hre : ∀ w : ℂ, ((w + 3) / 6).re = (w.re + 3) / 6 := by
    intro w
    simp [add_re, div_ofNat_re]
  have hre' : ∀ s : ℂ, (6 * s - 3).re = 6 * s.re - 3 := by
    intro s
    simp only [sub_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]
  constructor
  · rintro ⟨G, hG, hGH, hG0⟩
    refine ⟨fun w => G ((w + 3) / 6) / E ((w + 3) / 6), ?_, ?_, ?_⟩
    · intro w hw
      have hw' : σ < ((w + 3) / 6).re := by
        rw [hre]
        have : 6 * σ - 3 < w.re := hw
        linarith
      have hlin : DifferentiableAt ℂ (fun w : ℂ => (w + 3) / 6) w := by fun_prop
      have hGat : DifferentiableAt ℂ G ((w + 3) / 6) :=
        hG.differentiableAt ((isOpen_lt continuous_const continuous_re).mem_nhds hw')
      have hEat : DifferentiableAt ℂ E ((w + 3) / 6) :=
        hEd.differentiableAt ((isOpen_lt continuous_const continuous_re).mem_nhds hw')
      have h1 : DifferentiableAt ℂ (fun w : ℂ => G ((w + 3) / 6)) w := hGat.comp w hlin
      have h2 : DifferentiableAt ℂ (fun w : ℂ => E ((w + 3) / 6)) w := hEat.comp w hlin
      exact (h1.div h2 (hE0 _ hw')).differentiableWithinAt
    · intro w hw
      have hs : 2 / 3 < ((w + 3) / 6).re := by rw [hre]; linarith
      have hw' : 6 * ((w + 3) / 6) - 3 = w := by ring
      show G ((w + 3) / 6) / E ((w + 3) / 6) = _
      rw [hGH _ hs, principalCorrection_eq_phaseLFunction_mul S hS4 A η hA hη hs, hw',
        mul_div_assoc, div_self (hE0 _ (by linarith)), mul_one]
    · intro w hw
      have hw' : σ < ((w + 3) / 6).re := by rw [hre]; linarith
      exact div_ne_zero (hG0 _ hw') (hE0 _ hw')
  · rintro ⟨Λ, hΛ, hΛL, hΛ0⟩
    refine ⟨fun s => Λ (6 * s - 3) * E s, ?_, ?_, ?_⟩
    · intro s hs
      have hs' : 6 * σ - 3 < (6 * s - 3).re := by
        rw [hre']
        have : σ < s.re := hs
        linarith
      have hlin : DifferentiableAt ℂ (fun s : ℂ => 6 * s - 3) s := by fun_prop
      have hΛat : DifferentiableAt ℂ Λ (6 * s - 3) :=
        hΛ.differentiableAt ((isOpen_lt continuous_const continuous_re).mem_nhds hs')
      exact ((hΛat.comp s hlin).mul
        (hEd.differentiableAt ((isOpen_lt continuous_const continuous_re).mem_nhds hs))).differentiableWithinAt
    · intro s hs
      have hτ : 1 < (6 * s - 3).re := by rw [hre']; linarith
      show Λ (6 * s - 3) * E s = _
      rw [principalCorrection_eq_phaseLFunction_mul S hS4 A η hA hη hs, hΛL _ hτ]
    · intro s hs
      have hs' : 6 * σ - 3 < (6 * s - 3).re := by rw [hre']; linarith
      exact mul_ne_zero (hΛ0 _ hs') (hE0 s hs)

end NumberField

/-! ### Below the wall the frame is a transport law -/

/-- **A zero of `L` is a zero of `E`.** If the signal of `G` is `O(Z^b)`, `b < 1`, and `G L = E`
on `Re s > 1` with `L, E` holomorphic on `Re s > b`, then every zero of `L` right of `b` is a zero
of `E`. -/
theorem eq_zero_of_signal_le_of_eq_zero {G L E : ℂ → ℂ} (hG : IsSignalKernel G) {b K Z₀ : ℝ}
    (hb : b < 1) (hZ₀ : 0 < Z₀) (hK : ∀ Z : ℝ, Z₀ ≤ Z → ‖signal G 2 Z‖ ≤ K * Z ^ b)
    (hL : DifferentiableOn ℂ L {s : ℂ | b < s.re}) (hE : DifferentiableOn ℂ E {s : ℂ | b < s.re})
    (hGL : ∀ s : ℂ, 1 < s.re → G s * L s = E s) {ρ : ℂ} (hρ : b < ρ.re) (h0 : L ρ = 0) :
    E ρ = 0 := by
  obtain ⟨F, hF, hFG⟩ := exists_differentiableOn_eq_of_signal_le hG (by linarith) hZ₀ hK
  rw [max_eq_right hb.le] at hFG
  have hopen : IsOpen {s : ℂ | b < s.re} := isOpen_lt continuous_const continuous_re
  have h2 : ((2 : ℝ) : ℂ) ∈ {s : ℂ | b < s.re} := by
    show b < ((2 : ℝ) : ℂ).re
    rw [ofReal_re]; linarith
  have hev : (fun s => F s * L s) =ᶠ[nhds ((2 : ℝ) : ℂ)] E := by
    have hnhds : {s : ℂ | 1 < s.re} ∈ nhds ((2 : ℝ) : ℂ) :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by
        show 1 < ((2 : ℝ) : ℂ).re
        rw [ofReal_re]; norm_num)
    filter_upwards [hnhds] with s hs
    rw [hFG s hs, hGL s hs]
  have heq := ((hF.mul hL).analyticOnNhd hopen).eqOn_of_preconnected_of_eventuallyEq
    (hE.analyticOnNhd hopen) (convex_halfSpace_re_gt b).isPreconnected h2 hev
  have := heq hρ
  simp only [Pi.mul_apply, h0, mul_zero] at this
  exact this.symm

section Hecke

variable {K : Type*} [Field K] [NumberField K] (𝔪 : Modulus K)

/-- **The frame with a correction that may vanish.** For a ray class character `ψ`, a correction
`H` holomorphic on `Re s > b` and bounded on `Re s ≥ 2`, and a sum `J` with a direct bound
`Z^{a₁}` and a comparison `Z^{a₂}` with the signal of `exp((s − c)²) H(s)/L(s, ψ)`: every zero
`ρ ≠ 1` of `L(s, ψ)` with `Re ρ > max(b, a₁, a₂)` is a zero of `H`. -/
theorem heckeLFunction_transport (ψ : HeckeCharacter 𝔪) {H : ℂ → ℂ} {b a₁ a₂ c C Z₀ : ℝ}
    (hb : b < 1) (ha₁ : a₁ < 1) (ha₂ : a₂ < 1) (hb1 : b ≤ 1)
    (hH : DifferentiableOn ℂ H {s : ℂ | b < s.re}) (hHb : ∀ s : ℂ, 2 ≤ s.re → ‖H s‖ ≤ C)
    (J : ℝ → ℂ) (hZ₀ : 1 ≤ Z₀) (hJ : ∀ Z : ℝ, Z₀ ≤ Z → ‖J Z‖ ≤ C * Z ^ a₁)
    (hJf : ∀ Z : ℝ, Z₀ ≤ Z →
      ‖J Z - signal (fun s : ℂ => cexp ((s - c) ^ 2) * H s / heckeLFunction 𝔪 ψ s) 2 Z‖ ≤
        C * Z ^ a₂)
    {ρ : ℂ} (hρ : max b (max a₁ a₂) < ρ.re) (hρ1 : ρ ≠ 1) (h0 : heckeLFunction 𝔪 ψ ρ = 0) :
    H ρ = 0 := by
  set G : ℂ → ℂ := fun s => cexp ((s - c) ^ 2) * H s / heckeLFunction 𝔪 ψ s with hGdef
  have hopen : IsOpen {s : ℂ | b < s.re} := isOpen_lt continuous_const continuous_re
  have hHat : ∀ s : ℂ, 1 < s.re → DifferentiableAt ℂ H s := fun s hs =>
    hH.differentiableAt (hopen.mem_nhds (show b < s.re by linarith))
  have hG : IsSignalKernel G :=
    isSignalKernel_gauss_mul_div_of_bounded (Real.exp_pos _)
      (fun s hs => differentiableAt_heckeLFunction 𝔪 ψ (ne_one_of_one_lt_re hs))
      (fun s hs => heckeLFunction_ne_zero_of_one_lt_re 𝔪 ψ hs)
      (fun s hs => by
        rw [heckeLFunction_eq_heckeL 𝔪 ψ (by linarith : (1 : ℝ) < s.re)]
        exact exp_neg_le_norm_heckeL 𝔪 ψ hs)
      hHat hHb c
  set m := max b (max a₁ a₂) with hmdef
  have hm : m < 1 := max_lt hb (max_lt ha₁ ha₂)
  -- the signal is `O(Z^m)`
  have hK : ∀ Z : ℝ, Z₀ ≤ Z → ‖signal G 2 Z‖ ≤ (2 * |C|) * Z ^ m := by
    intro Z hZ
    have hZ1 : 1 ≤ Z := le_trans hZ₀ hZ
    have h1 : Z ^ a₁ ≤ Z ^ m :=
      Real.rpow_le_rpow_of_exponent_le hZ1 ((le_max_left _ _).trans (le_max_right _ _))
    have h2 : Z ^ a₂ ≤ Z ^ m :=
      Real.rpow_le_rpow_of_exponent_le hZ1 ((le_max_right _ _).trans (le_max_right _ _))
    have hpos1 : 0 ≤ Z ^ a₁ := Real.rpow_nonneg (by linarith) _
    have hpos2 : 0 ≤ Z ^ a₂ := Real.rpow_nonneg (by linarith) _
    calc ‖signal G 2 Z‖ = ‖J Z - (J Z - signal G 2 Z)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖J Z‖ + ‖J Z - signal G 2 Z‖ := norm_sub_le _ _
      _ ≤ C * Z ^ a₁ + C * Z ^ a₂ := add_le_add (hJ Z hZ) (hJf Z hZ)
      _ ≤ |C| * Z ^ m + |C| * Z ^ m :=
          add_le_add
            (le_trans (mul_le_mul_of_nonneg_right (le_abs_self C) hpos1)
              (mul_le_mul_of_nonneg_left h1 (abs_nonneg C)))
            (le_trans (mul_le_mul_of_nonneg_right (le_abs_self C) hpos2)
              (mul_le_mul_of_nonneg_left h2 (abs_nonneg C)))
      _ = 2 * |C| * Z ^ m := by ring
  have hmb : b ≤ m := le_max_left _ _
  have hopenm : IsOpen {s : ℂ | m < s.re} := isOpen_lt continuous_const continuous_re
  have hHm : DifferentiableOn ℂ H {s : ℂ | m < s.re} :=
    hH.mono fun s hs => lt_of_le_of_lt hmb hs
  -- apply the zero lemma to the zero function of `ψ`
  have hE := eq_zero_of_signal_le_of_eq_zero (L := heckeZeroFunction 𝔪 ψ)
    (E := fun s => cexp ((s - c) ^ 2) * H s * (if ψ = 1 then s - 1 else 1)) hG hm
    (by linarith) hK (differentiable_heckeZeroFunction 𝔪 ψ).differentiableOn
    (by
      refine (((by fun_prop : Differentiable ℂ fun s : ℂ =>
        cexp ((s - c) ^ 2)).differentiableOn).mul hHm).mul ?_
      split_ifs
      · exact (differentiable_id.sub_const 1).differentiableOn
      · exact differentiableOn_const 1)
    (fun s hs => by
      have hL0 := heckeLFunction_ne_zero_of_one_lt_re 𝔪 ψ hs
      show cexp ((s - c) ^ 2) * H s / heckeLFunction 𝔪 ψ s * heckeZeroFunction 𝔪 ψ s =
        cexp ((s - c) ^ 2) * H s * (if ψ = 1 then s - 1 else 1)
      unfold heckeZeroFunction
      split_ifs
      · rw [heckePoleCleared_eq 𝔪 ψ (ne_one_of_one_lt_re hs)]
        field_simp
      · field_simp)
    hρ (by
      unfold heckeZeroFunction
      split_ifs
      · rw [heckePoleCleared_eq 𝔪 ψ hρ1, h0, mul_zero]
      · exact h0)
  have hfac : (if ψ = 1 then ρ - 1 else 1) ≠ 0 := by
    split_ifs
    · exact sub_ne_zero.mpr hρ1
    · exact one_ne_zero
  have := hE
  simp only at this
  rcases mul_eq_zero.mp this with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' (Complex.exp_ne_zero _)
    · exact h'
  · exact absurd h hfac

/-- **Transport through the phase `L`-function.** If the correction of the frame is
`H(s) = Λ(6s − 3) E(s)` on `Re s > b`, with `E` without zeros there, then under the two estimates
every zero `ρ ≠ 1` of `L(s, ψ)` with `Re ρ > max(b, a₁, a₂)` gives a zero `6ρ − 3` of `Λ`. -/
theorem heckeLFunction_transport_phase (ψ : HeckeCharacter 𝔪) {H Λ E : ℂ → ℂ}
    {b a₁ a₂ c C Z₀ : ℝ} (hb : b < 1) (ha₁ : a₁ < 1) (ha₂ : a₂ < 1)
    (hH : DifferentiableOn ℂ H {s : ℂ | b < s.re}) (hHb : ∀ s : ℂ, 2 ≤ s.re → ‖H s‖ ≤ C)
    (hHΛ : ∀ s : ℂ, b < s.re → H s = Λ (6 * s - 3) * E s)
    (hE0 : ∀ s : ℂ, b < s.re → E s ≠ 0)
    (J : ℝ → ℂ) (hZ₀ : 1 ≤ Z₀) (hJ : ∀ Z : ℝ, Z₀ ≤ Z → ‖J Z‖ ≤ C * Z ^ a₁)
    (hJf : ∀ Z : ℝ, Z₀ ≤ Z →
      ‖J Z - signal (fun s : ℂ => cexp ((s - c) ^ 2) * H s / heckeLFunction 𝔪 ψ s) 2 Z‖ ≤
        C * Z ^ a₂)
    {ρ : ℂ} (hρ : max b (max a₁ a₂) < ρ.re) (hρ1 : ρ ≠ 1) (h0 : heckeLFunction 𝔪 ψ ρ = 0) :
    Λ (6 * ρ - 3) = 0 := by
  have hHρ := heckeLFunction_transport 𝔪 ψ hb ha₁ ha₂ hb.le hH hHb J hZ₀ hJ hJf hρ hρ1 h0
  have hbρ : b < ρ.re := lt_of_le_of_lt (le_max_left _ _) hρ
  rw [hHΛ ρ hbρ] at hHρ
  exact (mul_eq_zero.mp hHρ).resolve_right (hE0 ρ hbρ)

end Hecke

end GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies
