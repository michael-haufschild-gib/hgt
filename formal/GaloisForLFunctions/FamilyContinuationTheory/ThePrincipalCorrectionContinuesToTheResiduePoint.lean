import GaloisForLFunctions.FamilyContinuationTheory.TheCorrectionOfAnUnramifiedRowHasNoPoleInW

/-!
# The principal correction continues to the residue point

The correction of the principal row, `H(x, w, z) = ∏_{v ∉ S} H_v(x, w, z)`, has at a good prime of
norm `n` the pole-free local factor `principalFactor` (the `rowH` form with `W = n^{−w}`,
`D = η(v) n^{−x}`, `R = κ⁶ n⁴ n^{−6x} n^{−6z}`). This module proves:

* `principalH_eq_principalFactor`: on the absolute region it is the factor of the Euler product,
  so `F₁ = ζ^S(6z) ζ^S(w) L^S(x, η)⁻¹ H` (`principalRow_eq_continued`);
* `norm_principalFactor_sub_one_le`: on `Re x ≥ 7/8`, `Re w ≥ 19/20`, `Re z ≥ 33/200`,
  `‖H_v − 1‖ ≤ 80 n^{−363/200}`;
* `differentiableOn_principalCorrectionC`: if `S` contains the primes of norm `≤ 160`, the
  product is holomorphic in each variable on the open region;
* `principalFactor_residue`: at `w = 1`, `z = 1/6` the factor is the local factor
  `h(x) = principalLocalFactor n (κ⁶) η(v) x` of the target correction.
-/

noncomputable section

open scoped BigOperators Classical

namespace GaloisForLFunctions.FamilyContinuationTheory

open IsDedekindDomain HeckeLFunctions MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein

/-- The pole-free local factor of the principal correction at a prime of norm `n`. -/
def principalFactor (n : ℕ) (κ ηp x w z : ℂ) : ℂ :=
  rowH (n : ℂ) ηp ((n : ℂ) ^ (-x)) ((n : ℂ) ^ (-w)) ((n : ℂ) ^ (-(6 * z)))
    (κ ^ 6 * (n : ℂ) ^ 4 * ((n : ℂ) ^ (-x)) ^ 6 * (n : ℂ) ^ (-(6 * z))) ((n : ℂ) ^ (-w))
    (ηp * (n : ℂ) ^ (-x))

/-- On the region of the Euler product the correction is the pole-free factor. -/
theorem principalH_eq_principalFactor (n : ℕ) (κ ηp x w z : ℂ)
    (hV : 1 - (n : ℂ) ^ (-(6 * z)) ≠ 0) (hY : 1 - (n : ℂ) ^ (-w) ≠ 0)
    (hR : 1 - κ ^ 6 * (n : ℂ) ^ 4 * ((n : ℂ) ^ (-x)) ^ 6 * (n : ℂ) ^ (-(6 * z)) ≠ 0)
    (hD : 1 - ηp * (n : ℂ) ^ (-x) ≠ 0) :
    principalH (n : ℂ) κ ηp ((n : ℂ) ^ (-x)) ((n : ℂ) ^ (-w)) ((n : ℂ) ^ (-(6 * z))) =
      principalFactor n κ ηp x w z := by
  unfold principalH principalSum principalFactor
  exact local_mul_eq_rowH _ _ _ _ _ _ _ _ hV hY hR hD

/-- **The local bound near the residue point.** -/
theorem norm_principalFactor_sub_one_le {n : ℕ} (hn : 7 ≤ n) {κ ηp : ℂ} (hκ : ‖κ‖ ≤ 1)
    (hη : ‖ηp‖ ≤ 1) {x w z : ℂ} (hx : 7 / 8 ≤ x.re) (hw : 19 / 20 ≤ w.re)
    (hz : 33 / 200 ≤ z.re) :
    ‖principalFactor n κ ηp x w z - 1‖ ≤ 80 * (n : ℝ) ^ (-(363 / 200 : ℝ)) := by
  have hn1 : 1 ≤ n := by omega
  have hX := norm_natCast_cpow_neg_le hn1 hx
  have hY := norm_natCast_cpow_neg_le hn1 hw
  have hV := norm_natCast_cpow_neg_le (x := 6 * z) hn1 (a := 99 / 100)
    (by simp [Complex.mul_re]; linarith)
  have hR : ‖κ ^ 6 * (n : ℂ) ^ 4 * ((n : ℂ) ^ (-x)) ^ 6 * (n : ℂ) ^ (-(6 * z))‖ ≤
      (n : ℝ) ^ 4 * ‖(n : ℂ) ^ (-x)‖ ^ 6 * ‖(n : ℂ) ^ (-(6 * z))‖ := by
    rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, norm_pow, Complex.norm_natCast]
    have : ‖κ‖ ^ 6 ≤ 1 := pow_le_one₀ (norm_nonneg _) hκ
    calc ‖κ‖ ^ 6 * (n : ℝ) ^ 4 * ‖(n : ℂ) ^ (-x)‖ ^ 6 * ‖(n : ℂ) ^ (-(6 * z))‖ ≤
        1 * (n : ℝ) ^ 4 * ‖(n : ℂ) ^ (-x)‖ ^ 6 * ‖(n : ℂ) ^ (-(6 * z))‖ := by gcongr
      _ = _ := by ring
  have hD : ‖ηp * (n : ℂ) ^ (-x)‖ ≤ ‖(n : ℂ) ^ (-x)‖ := by
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hη
  have h := norm_rowH_sub_one_le_D2 (Q := (n : ℝ)) (by exact_mod_cast hn) hX hY hY hV hD hR hη
  rw [Complex.ofReal_natCast] at h
  exact h

/-- **At the double residue** the factor is the local factor of the target correction. -/
theorem principalFactor_residue {n : ℕ} (hn : 2 ≤ n) (κ ηp x : ℂ)
    (hD : 1 - ηp * ((n : ℝ) : ℂ) ^ (-x) ≠ 0)
    (hR : 1 - κ ^ 6 * ((n : ℝ) : ℂ) ^ (3 - 6 * x) ≠ 0) :
    principalFactor n κ ηp x 1 (1 / 6) = principalLocalFactor (n : ℝ) (κ ^ 6) ηp x := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnC : ((n : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn0.ne'
  have hq : 1 - ((n : ℝ) : ℂ)⁻¹ ≠ 0 := by
    intro h
    have h1 : ((n : ℝ) : ℂ) = 1 := by
      have := inv_eq_one.mp (by linear_combination -h : ((n : ℝ) : ℂ)⁻¹ = 1)
      exact this
    have : (n : ℝ) = 1 := by exact_mod_cast h1
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hinv : ((n : ℝ) : ℂ) ^ (-(1 : ℂ)) = ((n : ℝ) : ℂ)⁻¹ := Complex.cpow_neg_one _
  have h6 : -(6 * (1 / 6 : ℂ)) = -1 := by norm_num
  rw [← principalH_residue hn0 κ ηp x hD hR hq]
  have hY : 1 - (n : ℂ) ^ (-(1 : ℂ)) ≠ 0 := by
    rw [← Complex.ofReal_natCast, hinv]
    exact hq
  have hRx : 1 - κ ^ 6 * (n : ℂ) ^ 4 * ((n : ℂ) ^ (-x)) ^ 6 * (n : ℂ) ^ (-(6 * (1 / 6 : ℂ))) ≠ 0 := by
    have hX6 : (((n : ℝ) : ℂ) ^ (-x)) ^ 6 = ((n : ℝ) : ℂ) ^ (-(6 * x)) := by
      rw [← Complex.cpow_nat_mul]
      ring_nf
    have h36 : ((n : ℝ) : ℂ) ^ (3 - 6 * x) = ((n : ℝ) : ℂ) ^ 3 * ((n : ℝ) : ℂ) ^ (-(6 * x)) := by
      rw [sub_eq_add_neg, Complex.cpow_add _ _ hnC, show ((3 : ℂ)) = ((3 : ℕ) : ℂ) by norm_num,
        Complex.cpow_natCast]
    rw [h6, ← Complex.ofReal_natCast, hX6, hinv]
    rw [h36] at hR
    convert hR using 2
    field_simp
  rw [← principalH_eq_principalFactor n κ ηp x 1 (1 / 6) (by rw [h6]; exact hY) hY hRx
    (by rwa [← Complex.ofReal_natCast])]
  rw [h6, ← Complex.ofReal_natCast, hinv]

/-! ### Holomorphy of the local factor -/

/-- The three denominators of the factor are at most `1/2` near the residue point. -/
theorem principalFactor_small {n : ℕ} (hn : 7 ≤ n) {κ ηp : ℂ} (hκ : ‖κ‖ ≤ 1) (hη : ‖ηp‖ ≤ 1)
    {x z : ℂ} (hx : 7 / 8 ≤ x.re) (hz : 33 / 200 ≤ z.re) :
    ‖(n : ℂ) ^ (-(6 * z))‖ ≤ 1 / 2 ∧
      ‖κ ^ 6 * (n : ℂ) ^ 4 * ((n : ℂ) ^ (-x)) ^ 6 * (n : ℂ) ^ (-(6 * z))‖ ≤ 1 / 2 ∧
        ‖ηp * (n : ℂ) ^ (-x)‖ ≤ 1 / 2 := by
  have hn1 : 1 ≤ n := by omega
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast (show 4 ≤ n by omega)
  have hn0 : (0 : ℝ) < n := by linarith
  have hX := norm_natCast_cpow_neg_le hn1 hx
  have hV := norm_natCast_cpow_neg_le (x := 6 * z) hn1 (a := 99 / 100)
    (by simp [Complex.mul_re]; linarith)
  have hX2 : ‖(n : ℂ) ^ (-x)‖ ≤ 1 / 2 := hX.trans (rpow_le_half_of_four_le hn4 (by norm_num))
  have hV2 : ‖(n : ℂ) ^ (-(6 * z))‖ ≤ 1 / 2 := hV.trans (rpow_le_half_of_four_le hn4 (by norm_num))
  refine ⟨hV2, ?_, ?_⟩
  · rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, norm_pow, Complex.norm_natCast]
    calc ‖κ‖ ^ 6 * (n : ℝ) ^ 4 * ‖(n : ℂ) ^ (-x)‖ ^ 6 * ‖(n : ℂ) ^ (-(6 * z))‖ ≤
        1 * (n : ℝ) ^ 4 * ((n : ℝ) ^ (-(7 / 8 : ℝ))) ^ 6 * (n : ℝ) ^ (-(99 / 100 : ℝ)) := by
          gcongr
          exact pow_le_one₀ (norm_nonneg _) hκ
      _ = (n : ℝ) ^ ((4 : ℝ) + (-(7 / 8 : ℝ)) * 6 + (-(99 / 100 : ℝ))) := by
          rw [one_mul, Real.rpow_add hn0, Real.rpow_add hn0, Real.rpow_mul hn0.le]
          norm_cast
      _ ≤ 1 / 2 := rpow_le_half_of_four_le hn4 (by norm_num)
  · rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hη).trans hX2

theorem one_sub_ne_zero_of_norm_le_half {a : ℂ} (ha : ‖a‖ ≤ 1 / 2) : 1 - a ≠ 0 := fun h => by
  rw [show a = 1 by linear_combination -h, norm_one] at ha
  norm_num at ha

/-- The factor is holomorphic in each variable near the residue point. -/
theorem principalFactor_differentiableAt {n : ℕ} (hn : 7 ≤ n) {κ ηp : ℂ} (hκ : ‖κ‖ ≤ 1)
    (hη : ‖ηp‖ ≤ 1) {x w z : ℂ} (hx : 7 / 8 ≤ x.re) (hz : 33 / 200 ≤ z.re) :
    DifferentiableAt ℂ (fun x => principalFactor n κ ηp x w z) x ∧
      DifferentiableAt ℂ (fun w => principalFactor n κ ηp x w z) w ∧
        DifferentiableAt ℂ (fun z => principalFactor n κ ηp x w z) z := by
  obtain ⟨hV, hR, hD⟩ := principalFactor_small hn hκ hη hx hz
  have hV' := one_sub_ne_zero_of_norm_le_half hV
  have hR' := one_sub_ne_zero_of_norm_le_half hR
  have hD' := one_sub_ne_zero_of_norm_le_half hD
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  unfold principalFactor rowH rowE
  refine ⟨?_, ?_, ?_⟩ <;> fun_prop (disch := first | assumption | exact Or.inl hn0)

/-! ### The continued correction -/

section Global

variable (𝔪 : Modulus K) (η : HeckeCharacter 𝔪)

/-- The phase `κ_v = ᾱ_v η(v)` of a prime. -/
def primeKappaAt (v : HeightOneSpectrum O) : ℂ :=
  primeKappa (primeGen v) (heckeValue 𝔪 η v.asIdeal)

/-- **The continued correction of the principal row**, `∏_{v ∉ S}` of the pole-free factors. -/
def principalCorrectionC (S : Finset (HeightOneSpectrum O)) (x w z : ℂ) : ℂ :=
  ∏' v : {v : HeightOneSpectrum O // v ∉ S},
    principalFactor v.1.asIdeal.absNorm (primeKappaAt 𝔪 η v.1) (heckeValue 𝔪 η v.1.asIdeal) x w z

theorem norm_primeKappaAt_le (v : HeightOneSpectrum O) : ‖primeKappaAt 𝔪 η v‖ ≤ 1 :=
  norm_primeKappa_le _ (norm_heckeValue_le_one 𝔪 η _)

/-- The defect majorant `80 N(v)^{−363/200}`. -/
def principalDefect (v : HeightOneSpectrum O) : ℝ :=
  80 * (v.asIdeal.absNorm : ℝ) ^ (-(363 / 200 : ℝ))

theorem summable_principalDefect (S : Finset (HeightOneSpectrum O)) :
    Summable fun v : {v : HeightOneSpectrum O // v ∉ S} => principalDefect v.1 :=
  ((numberField_summable_finitePlace_absNorm_rpow (K := K) (σ := 363 / 200)
    (by norm_num)).subtype _).mul_left 80

theorem principalDefect_le_half {v : HeightOneSpectrum O} (hv : 160 < v.asIdeal.absNorm) :
    principalDefect v ≤ 1 / 2 := by
  have hn : (161 : ℝ) ≤ v.asIdeal.absNorm := by exact_mod_cast hv
  unfold principalDefect
  calc 80 * (v.asIdeal.absNorm : ℝ) ^ (-(363 / 200 : ℝ)) ≤
      80 * (v.asIdeal.absNorm : ℝ) ^ (-(1 : ℝ)) := by
        gcongr
        · linarith
        · norm_num
    _ = 80 * (v.asIdeal.absNorm : ℝ)⁻¹ := by rw [Real.rpow_neg_one]
    _ ≤ 1 / 2 := by
        rw [← div_eq_mul_inv, div_le_iff₀ (by linarith)]
        linarith

/-- **Holomorphy of the continued correction**, in each variable, on the open region
`Re x > 7/8`, `Re w > 19/20`, `Re z > 33/200`, when `S` contains the primes of norm `≤ 160`. -/
theorem differentiableOn_principalCorrectionC (S : Finset (HeightOneSpectrum O))
    (hS : ∀ v : HeightOneSpectrum O, v.asIdeal.absNorm ≤ 160 → v ∈ S) {x w z : ℂ}
    (hx : 7 / 8 ≤ x.re) (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    DifferentiableOn ℂ (fun x => principalCorrectionC 𝔪 η S x w z) {x | 7 / 8 < x.re} ∧
      DifferentiableOn ℂ (fun w => principalCorrectionC 𝔪 η S x w z) {w | 19 / 20 < w.re} ∧
        DifferentiableOn ℂ (fun z => principalCorrectionC 𝔪 η S x w z) {z | 33 / 200 < z.re} := by
  have hlarge : ∀ v : {v : HeightOneSpectrum O // v ∉ S}, 160 < v.1.asIdeal.absNorm := fun v =>
    lt_of_not_ge fun h => v.2 (hS _ h)
  have hn7 : ∀ v : {v : HeightOneSpectrum O // v ∉ S}, 7 ≤ v.1.asIdeal.absNorm := fun v => by
    have := hlarge v
    omega
  have hb := summable_principalDefect S
  have hb2 : ∀ v : {v : HeightOneSpectrum O // v ∉ S}, principalDefect v.1 ≤ 1 / 2 := fun v =>
    principalDefect_le_half (hlarge v)
  have hbound : ∀ (v : {v : HeightOneSpectrum O // v ∉ S}) {x w z : ℂ}, 7 / 8 ≤ x.re →
      19 / 20 ≤ w.re → 33 / 200 ≤ z.re →
      ‖principalFactor v.1.asIdeal.absNorm (primeKappaAt 𝔪 η v.1) (heckeValue 𝔪 η v.1.asIdeal)
        x w z - 1‖ ≤ principalDefect v.1 := fun v x w z hx hw hz =>
    norm_principalFactor_sub_one_le (hn7 v) (norm_primeKappaAt_le 𝔪 η v.1)
      (norm_heckeValue_le_one 𝔪 η _) hx hw hz
  have hdiff : ∀ (v : {v : HeightOneSpectrum O // v ∉ S}) {x w z : ℂ}, 7 / 8 ≤ x.re →
      33 / 200 ≤ z.re →
      DifferentiableAt ℂ (fun x => principalFactor v.1.asIdeal.absNorm (primeKappaAt 𝔪 η v.1)
          (heckeValue 𝔪 η v.1.asIdeal) x w z) x ∧
        DifferentiableAt ℂ (fun w => principalFactor v.1.asIdeal.absNorm (primeKappaAt 𝔪 η v.1)
          (heckeValue 𝔪 η v.1.asIdeal) x w z) w ∧
          DifferentiableAt ℂ (fun z => principalFactor v.1.asIdeal.absNorm (primeKappaAt 𝔪 η v.1)
            (heckeValue 𝔪 η v.1.asIdeal) x w z) z := fun v x w z hx hz =>
    principalFactor_differentiableAt (hn7 v) (norm_primeKappaAt_le 𝔪 η v.1)
      (norm_heckeValue_le_one 𝔪 η v.1.asIdeal) hx hz
  have hUx : IsOpen {x : ℂ | 7 / 8 < x.re} := isOpen_lt continuous_const Complex.continuous_re
  have hUw : IsOpen {w : ℂ | 19 / 20 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hUz : IsOpen {z : ℂ | 33 / 200 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  refine ⟨?_, ?_, ?_⟩
  · exact (hasProd_and_bounds_of_defect hUx hb
      (fun v x' hx' => ((hdiff v (x := x') (w := w) (le_of_lt hx') hz).1).differentiableWithinAt)
      (fun v x' hx' => hbound v (le_of_lt hx') hw hz) hb2).1
  · exact (hasProd_and_bounds_of_defect hUw hb
      (fun v w' _ => ((hdiff v (x := x) (w := w') hx hz).2.1).differentiableWithinAt)
      (fun v w' hw' => hbound v hx (le_of_lt hw') hz) hb2).1
  · exact (hasProd_and_bounds_of_defect hUz hb
      (fun v z' hz' => ((hdiff v (x := x) (w := w) hx (le_of_lt hz')).2.2).differentiableWithinAt)
      (fun v z' hz' => hbound v hx hw (le_of_lt hz')) hb2).1

/-- **The principal row with the continued correction**: on `Re x ≥ 3`, `Re w ≥ 3`, `Re z ≥ 2`,
`F₁ = ζ^S(6z) ζ^S(w) L^S(x, η)⁻¹ H(x, w, z)` with the pole-free factors. -/
theorem principalRow_eq_continued (S : Finset (HeightOneSpectrum O))
    (hS : ∀ v : HeightOneSpectrum O, (lambda ∈ v.asIdeal ∨ (2 : O) ∈ v.asIdeal) → v ∈ S)
    {x w z : ℂ} (hx : 3 ≤ x.re) (hw : 3 ≤ w.re) (hz : 2 ≤ z.re) :
    principalRow 𝔪 η S x w z =
      zetaS S (6 * z) * zetaS S w * heckeInvS 𝔪 η S x * principalCorrectionC 𝔪 η S x w z := by
  rw [principalRow_eq 𝔪 η S hS hx hw hz]
  congr 1
  unfold principalRowCorrection principalCorrectionC
  refine tprod_congr fun v => ?_
  have hlam : lambda ∉ v.1.asIdeal := fun h => v.2 (hS _ (Or.inl h))
  have hn2 : 2 ≤ v.1.asIdeal.absNorm := ArtinMertens.two_le_absNorm_of_isPrime v.1.isPrime v.1.ne_bot
  have hn1 : 1 ≤ v.1.asIdeal.absNorm := by omega
  set n := v.1.asIdeal.absNorm
  have hhalf : ∀ {a : ℝ}, 1 ≤ a → (n : ℝ) ^ (-a) ≤ 1 / 2 := fun ha => by
    have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    calc (n : ℝ) ^ (-_) ≤ (n : ℝ) ^ (-(1 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = (n : ℝ)⁻¹ := Real.rpow_neg_one _
      _ ≤ 1 / 2 := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have hX := norm_natCast_cpow_neg_le hn1 hx
  have hY := norm_natCast_cpow_neg_le hn1 hw
  have hV := norm_natCast_cpow_neg_le (x := 6 * z) hn1 (a := 12)
    (by simp [Complex.mul_re]; linarith)
  have hκ := norm_primeKappaAt_le 𝔪 η v.1
  have hη := norm_heckeValue_le_one 𝔪 η v.1.asIdeal
  rw [primeQ_primeGen v.1 hlam]
  refine principalH_eq_principalFactor n _ _ x w z
    (one_sub_ne_zero_of_norm_le_half (hV.trans (hhalf (by norm_num))))
    (one_sub_ne_zero_of_norm_le_half (hY.trans (hhalf (by norm_num)))) ?_
    (one_sub_ne_zero_of_norm_le_half ?_)
  · refine one_sub_ne_zero_of_norm_le_half ?_
    rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, norm_pow, Complex.norm_natCast]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    calc ‖primeKappa (primeGen v.1) (heckeValue 𝔪 η v.1.asIdeal)‖ ^ 6 * (n : ℝ) ^ 4 *
          ‖(n : ℂ) ^ (-x)‖ ^ 6 * ‖(n : ℂ) ^ (-(6 * z))‖ ≤
        1 * (n : ℝ) ^ 4 * ((n : ℝ) ^ (-(3 : ℝ))) ^ 6 * (n : ℝ) ^ (-(12 : ℝ)) := by
          gcongr
          exact pow_le_one₀ (norm_nonneg _) hκ
      _ = (n : ℝ) ^ ((4 : ℝ) + (-(3 : ℝ)) * 6 + (-(12 : ℝ))) := by
          rw [one_mul, Real.rpow_add hn0, Real.rpow_add hn0, Real.rpow_mul hn0.le]
          norm_cast
      _ = (n : ℝ) ^ (-(26 : ℝ)) := by norm_num
      _ ≤ 1 / 2 := hhalf (by norm_num)
  · rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hη).trans (hX.trans (hhalf (by norm_num)))

/-- **At the double residue the continued correction is the target correction** of
`TheCorrectionOfThePrincipalRowIsAConvergentEulerProduct`, with the phases `A_v = κ_v⁶`, on
`Re x ≥ 7/8`, when `S` contains the primes of norm `≤ 160`. -/
theorem principalCorrectionC_residue (S : Finset (HeightOneSpectrum O))
    (hS : ∀ v : HeightOneSpectrum O, v.asIdeal.absNorm ≤ 160 → v ∈ S) {x : ℂ}
    (hx : 7 / 8 ≤ x.re) :
    principalCorrectionC 𝔪 η S x 1 (1 / 6) =
      principalCorrection (fun v => primeKappaAt 𝔪 η v ^ 6) (fun v => heckeValue 𝔪 η v.asIdeal)
        S x := by
  unfold principalCorrectionC principalCorrection
  refine tprod_congr fun v => ?_
  have hlarge : 160 < v.1.asIdeal.absNorm := lt_of_not_ge fun h => v.2 (hS _ h)
  have hn7 : 7 ≤ v.1.asIdeal.absNorm := by omega
  obtain ⟨-, hR, hD⟩ := principalFactor_small hn7 (norm_primeKappaAt_le 𝔪 η v.1)
    (norm_heckeValue_le_one 𝔪 η v.1.asIdeal) (z := 1 / 6) hx (by norm_num)
  have hn0 : ((v.1.asIdeal.absNorm : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (show v.1.asIdeal.absNorm ≠ 0 by omega)
  refine principalFactor_residue (by omega) _ _ _ ?_ ?_
  · rw [Complex.ofReal_natCast]
    exact one_sub_ne_zero_of_norm_le_half hD
  · refine one_sub_ne_zero_of_norm_le_half (le_of_eq_of_le ?_ hR)
    have hX6 : (((v.1.asIdeal.absNorm : ℕ) : ℂ) ^ (-x)) ^ 6 =
        ((v.1.asIdeal.absNorm : ℕ) : ℂ) ^ (-(6 * x)) := by
      rw [← Complex.cpow_nat_mul]
      ring_nf
    have h36 : ((v.1.asIdeal.absNorm : ℕ) : ℂ) ^ (3 - 6 * x) =
        ((v.1.asIdeal.absNorm : ℕ) : ℂ) ^ 3 * ((v.1.asIdeal.absNorm : ℕ) : ℂ) ^ (-(6 * x)) := by
      rw [sub_eq_add_neg, Complex.cpow_add _ _ hn0, show ((3 : ℂ)) = ((3 : ℕ) : ℂ) by norm_num,
        Complex.cpow_natCast]
    have h6 : -(6 * (1 / 6 : ℂ)) = -1 := by norm_num
    rw [Complex.ofReal_natCast, h36, hX6, h6, Complex.cpow_neg_one]
    congr 1
    field_simp

end Global

end GaloisForLFunctions.FamilyContinuationTheory
