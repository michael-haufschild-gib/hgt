import GaloisForLFunctions.RHTower.XiResolventMassDecay

/-!
# The unconditional sector of the resolvent Hankel criterion

RH is equivalent to positive semidefiniteness of the resolvent Hankel array at any one shift
`X ≥ 0`.  This file proves that a growing sector of that criterion holds **unconditionally**.

The mechanism is a cone law with a degree-dependent aperture.  The height gap `2 < g^2` and the
critical strip `|b| < 1/2` place every shifted squared spectral point `w = (g + b i)^2 + X` in the
sector `(2n+1) |Im w| < Re w` as soon as `X ≥ ((2n+1)^2 + 1)/4` — by the arithmetic–geometric mean
inequality `(2n+1) g ≤ g^2 + (2n+1)^2/4`, with no square roots.  The sector is inherited by the
resolvent coordinate `u = w⁻¹`, and an elementary Bernoulli–geometric-series estimate shows that a
sector element of aperture `1/(2n+1)` keeps all powers up to `n+1` in the open right half-plane:

`Re (z^(n+1)) ≥ (Re z)^(n+1) - (n+1) |Im z| (Re z + |Im z|)^n > 0`.

Consequences, all unconditional:

* every resolvent moment `R n X = sum_q u_q^(n+1)` has strictly positive real part once
  `X ≥ (n+1)^2` — the diagonal of the Hankel criterion holds to **unbounded degree** with a
  quadratic shift law;
* the Hankel quadratic form is nonnegative — strictly positive for a nonzero weight — on the whole
  cone of **nonnegative coefficient vectors** once `X ≥ (2N+1)^2`;
* hence any coefficient vector witnessing Hankel negativity at such a shift must change sign.

Together with the corpus equivalence `RH ↔ all Hankel forms nonnegative at one shift` and the mass
bounds `|failure| ≤ 2 L^2 M(X)`, `M(X) ≤ 2H/(X+1)^2`, this pins the RH obstruction precisely: it is
invisible to every linear (moment) test and to every one-signed quadratic test, and can live only
in sign-changing bilinear tests against the deviation mass `M(X)`.
-/

open Complex

namespace RHTower

noncomputable section

/-! ## §1 Sector powers stay in the right half-plane -/

/-- Bernoulli-type bound `(a - n b) a^n ≤ (a - b)^n a` for `0 ≤ b ≤ a`. -/
theorem sub_nat_mul_mul_pow_le {a b : ℝ} (hb : 0 ≤ b) (hba : b ≤ a) (n : ℕ) :
    (a - n * b) * a ^ n ≤ (a - b) ^ n * a := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ha : 0 ≤ a := hb.trans hba
    have hab : 0 ≤ a - b := by linarith
    have hpow : 0 ≤ a ^ n := pow_nonneg ha n
    have h1 : (a - n * b) * a ^ n * (a - b) ≤ (a - b) ^ n * a * (a - b) :=
      mul_le_mul_of_nonneg_right ih hab
    have hnb : 0 ≤ (n : ℝ) * b ^ 2 * a ^ n := by positivity
    calc (a - ((n + 1 : ℕ) : ℝ) * b) * a ^ (n + 1)
        = (a - n * b) * a ^ n * (a - b) - (n : ℝ) * b ^ 2 * a ^ n := by push_cast; ring
      _ ≤ (a - n * b) * a ^ n * (a - b) := by linarith
      _ ≤ (a - b) ^ n * a * (a - b) := h1
      _ = (a - b) ^ (n + 1) * a := by ring

/-- Sector-power gap: `(2n+1) b < a` with `0 ≤ b` forces `(n+1) b (a+b)^n < a^(n+1)`. -/
theorem sector_pow_gap {a b : ℝ} (hb : 0 ≤ b) (n : ℕ) (hsec : (2 * n + 1) * b < a) :
    ((n : ℝ) + 1) * b * (a + b) ^ n < a ^ (n + 1) := by
  have hnn : (0 : ℝ) ≤ (2 * n + 1) * b := by positivity
  have ha : 0 < a := lt_of_le_of_lt hnn hsec
  have hba : b ≤ a := by nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ 2 * (n:ℝ)) hb]
  have hab : 0 ≤ a + b := by linarith
  have h1 : (a + b) ^ n * (a - b) ^ n ≤ a ^ (2 * n) := by
    have hprod : (a + b) * (a - b) ≤ a ^ 2 := by nlinarith [sq_nonneg b]
    have hprodnn : 0 ≤ (a + b) * (a - b) := mul_nonneg hab (by linarith)
    calc (a + b) ^ n * (a - b) ^ n = ((a + b) * (a - b)) ^ n := (mul_pow _ _ n).symm
      _ ≤ (a ^ 2) ^ n := pow_le_pow_left₀ hprodnn hprod n
      _ = a ^ (2 * n) := by rw [← pow_mul]
  have hbern := sub_nat_mul_mul_pow_le hb hba n
  have h2 : (a - n * b) * ((a + b) ^ n * a ^ n) ≤ a ^ (n + 1) * a ^ n := by
    have habn : 0 ≤ (a + b) ^ n := pow_nonneg hab n
    calc (a - n * b) * ((a + b) ^ n * a ^ n)
        = (a - n * b) * a ^ n * (a + b) ^ n := by ring
      _ ≤ (a - b) ^ n * a * (a + b) ^ n := mul_le_mul_of_nonneg_right hbern habn
      _ = (a + b) ^ n * (a - b) ^ n * a := by ring
      _ ≤ a ^ (2 * n) * a := mul_le_mul_of_nonneg_right h1 ha.le
      _ = a ^ (n + 1) * a ^ n := by ring
  have h3 : ((n : ℝ) + 1) * b < a - n * b := by nlinarith
  have hposmul : 0 < (a + b) ^ n * a ^ n := by positivity
  have h4 : ((n : ℝ) + 1) * b * ((a + b) ^ n * a ^ n) <
      (a - n * b) * ((a + b) ^ n * a ^ n) := mul_lt_mul_of_pos_right h3 hposmul
  have h5 : ((n : ℝ) + 1) * b * (a + b) ^ n * a ^ n < a ^ (n + 1) * a ^ n := by
    calc ((n : ℝ) + 1) * b * (a + b) ^ n * a ^ n
        = ((n : ℝ) + 1) * b * ((a + b) ^ n * a ^ n) := by ring
      _ < (a - n * b) * ((a + b) ^ n * a ^ n) := h4
      _ ≤ a ^ (n + 1) * a ^ n := h2
  exact lt_of_mul_lt_mul_right h5 (pow_nonneg ha.le n)

/-- Geometric-series estimate for the drift of a power from its real part:
`‖z^(n+1) - (Re z)^(n+1)‖ ≤ (n+1) |Im z| (Re z + |Im z|)^n` when `0 ≤ Re z`. -/
theorem norm_pow_sub_re_pow_le (z : ℂ) (hre : 0 ≤ z.re) (n : ℕ) :
    ‖z ^ (n + 1) - ((z.re : ℂ)) ^ (n + 1)‖ ≤
      ((n : ℝ) + 1) * |z.im| * (z.re + |z.im|) ^ n := by
  have hgeom := geom_sum₂_mul z ((z.re : ℂ)) (n + 1)
  rw [← hgeom, norm_mul]
  have hdiff : z - (z.re : ℂ) = (z.im : ℂ) * I := by
    apply Complex.ext <;> simp
  have hnormdiff : ‖z - (z.re : ℂ)‖ = |z.im| := by
    rw [hdiff, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [hnormdiff]
  have hbound : ‖∑ i ∈ Finset.range (n + 1), z ^ i * ((z.re : ℂ)) ^ (n + 1 - 1 - i)‖ ≤
      ((n : ℝ) + 1) * (z.re + |z.im|) ^ n := by
    have hM : 0 ≤ z.re + |z.im| := by positivity
    calc ‖∑ i ∈ Finset.range (n + 1), z ^ i * ((z.re : ℂ)) ^ (n + 1 - 1 - i)‖
        ≤ ∑ i ∈ Finset.range (n + 1), ‖z ^ i * ((z.re : ℂ)) ^ (n + 1 - 1 - i)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _i ∈ Finset.range (n + 1), (z.re + |z.im|) ^ n := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg hre]
          have hz : ‖z‖ ≤ z.re + |z.im| := by
            have h := Complex.norm_le_abs_re_add_abs_im z
            rwa [abs_of_nonneg hre] at h
          have hre' : z.re ≤ z.re + |z.im| := by
            have := abs_nonneg z.im; linarith
          have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          calc ‖z‖ ^ i * z.re ^ (n + 1 - 1 - i)
              ≤ (z.re + |z.im|) ^ i * (z.re + |z.im|) ^ (n + 1 - 1 - i) :=
                mul_le_mul (pow_le_pow_left₀ (norm_nonneg z) hz i)
                  (pow_le_pow_left₀ hre hre' _) (pow_nonneg hre _) (pow_nonneg hM i)
            _ = (z.re + |z.im|) ^ (i + (n + 1 - 1 - i)) := (pow_add _ _ _).symm
            _ = (z.re + |z.im|) ^ n := by
                congr 1
                simpa using Nat.add_sub_cancel' hin
      _ = ((n : ℝ) + 1) * (z.re + |z.im|) ^ n := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  calc ‖∑ i ∈ Finset.range (n + 1), z ^ i * ((z.re : ℂ)) ^ (n + 1 - 1 - i)‖ * |z.im|
      ≤ ((n : ℝ) + 1) * (z.re + |z.im|) ^ n * |z.im| :=
        mul_le_mul_of_nonneg_right hbound (abs_nonneg _)
    _ = ((n : ℝ) + 1) * |z.im| * (z.re + |z.im|) ^ n := by ring

/-- **Sector power floor.** -/
theorem re_pow_ge_of_re_nonneg (z : ℂ) (hre : 0 ≤ z.re) (n : ℕ) :
    z.re ^ (n + 1) - ((n : ℝ) + 1) * |z.im| * (z.re + |z.im|) ^ n ≤ (z ^ (n + 1)).re := by
  have hb := norm_pow_sub_re_pow_le z hre n
  have hsplit : (z ^ (n + 1)).re =
      z.re ^ (n + 1) + (z ^ (n + 1) - ((z.re : ℂ)) ^ (n + 1)).re := by
    rw [Complex.sub_re]
    have h : (((z.re : ℂ)) ^ (n + 1)).re = z.re ^ (n + 1) := by
      rw [← Complex.ofReal_pow, Complex.ofReal_re]
    rw [h]; ring
  rw [hsplit]
  have habs := Complex.abs_re_le_norm (z ^ (n + 1) - ((z.re : ℂ)) ^ (n + 1))
  have hneg := neg_abs_le ((z ^ (n + 1) - ((z.re : ℂ)) ^ (n + 1)).re)
  linarith

/-- **Sector power positivity**: aperture `1/(2n+1)` keeps all powers up to `n+1` in the open
right half-plane. -/
theorem re_pow_pos_of_sector (z : ℂ) (n : ℕ) (hsec : (2 * n + 1) * |z.im| < z.re) :
    0 < (z ^ (n + 1)).re := by
  have hre : 0 < z.re := lt_of_le_of_lt (by positivity) hsec
  have hgap := sector_pow_gap (abs_nonneg z.im) n hsec
  have hfloor := re_pow_ge_of_re_nonneg z hre.le n
  linarith

/-! ## §2 The divisor cone at quadratic shift -/

/-- The sector threshold is monotone in the degree. -/
theorem resolventSector_threshold_mono {m n : ℕ} (h : m ≤ n) :
    ((2 * (m : ℝ) + 1) ^ 2 + 1) / 4 ≤ ((2 * (n : ℝ) + 1) ^ 2 + 1) / 4 := by
  have hc : (m : ℝ) ≤ n := Nat.cast_le.mpr h
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  nlinarith [mul_nonneg (sub_nonneg.mpr hc) (by positivity : (0:ℝ) ≤ (n : ℝ) + m + 1)]

/-- **The divisor cone law**: at shift `X ≥ ((2n+1)^2 + 1)/4` every shifted squared spectral point
lies in the sector `(2n+1)|Im w| < Re w`.  Height gap bounds the numerator, the strip halves it,
and the arithmetic–geometric mean inequality supplies the aperture. -/
theorem sector_xiSpectralSq_add (n : ℕ) {X : ℝ}
    (hX : ((2 * (n : ℝ) + 1) ^ 2 + 1) / 4 ≤ X) (q : XiZeroCopy) :
    (2 * (n : ℝ) + 1) * |(xiSpectralPoint q ^ 2 + (X : ℂ)).im| <
      (xiSpectralPoint q ^ 2 + (X : ℂ)).re := by
  have hγ : 2 < (xiSpectralPoint q).re ^ 2 := by
    have h := xiZeroCopy_two_lt_im_sq q
    rwa [← xiSpectralPoint_re_eq] at h
  have hb : |(xiSpectralPoint q).im| < 1 / 2 := abs_xiSpectralPoint_im_lt_half q
  set γ := (xiSpectralPoint q).re with hγdef
  set b := (xiSpectralPoint q).im with hbdef
  have him : (xiSpectralPoint q ^ 2 + (X : ℂ)).im = 2 * γ * b := by
    rw [Complex.add_im, Complex.ofReal_im, sq, Complex.mul_im, ← hγdef, ← hbdef]
    ring
  have hre : (xiSpectralPoint q ^ 2 + (X : ℂ)).re = γ ^ 2 - b ^ 2 + X := by
    rw [Complex.add_re, Complex.ofReal_re, sq, Complex.mul_re, ← hγdef, ← hbdef]
    ring
  rw [him, hre]
  have hγpos : 1 < |γ| := by nlinarith [sq_abs γ, abs_nonneg γ]
  have habs : |2 * γ * b| = 2 * |γ| * |b| := by
    rw [abs_mul, abs_mul, abs_two]
  have hstep1 : (2 * (n : ℝ) + 1) * (2 * |γ| * |b|) < (2 * (n : ℝ) + 1) * |γ| := by
    have hlt : 2 * |γ| * |b| < |γ| := by nlinarith [abs_nonneg γ, abs_nonneg b]
    exact mul_lt_mul_of_pos_left hlt (by positivity)
  have hstep2 : (2 * (n : ℝ) + 1) * |γ| ≤ γ ^ 2 + (X - 1 / 4) := by
    nlinarith [sq_nonneg (|γ| - (2 * (n : ℝ) + 1) / 2), sq_abs γ]
  have hb2 : b ^ 2 ≤ 1 / 4 := by nlinarith [sq_abs b, abs_nonneg b]
  calc (2 * (n : ℝ) + 1) * |2 * γ * b|
      = (2 * (n : ℝ) + 1) * (2 * |γ| * |b|) := by rw [habs]
    _ < (2 * (n : ℝ) + 1) * |γ| := hstep1
    _ ≤ γ ^ 2 + (X - 1 / 4) := hstep2
    _ ≤ γ ^ 2 - b ^ 2 + X := by linarith

/-- The cone transfers to the resolvent coordinate under inversion. -/
theorem sector_xiResolventPoint (n : ℕ) {X : ℝ}
    (hX : ((2 * (n : ℝ) + 1) ^ 2 + 1) / 4 ≤ X) (q : XiZeroCopy) :
    (2 * (n : ℝ) + 1) * |(xiResolventPoint X q).im| < (xiResolventPoint X q).re := by
  have hX0 : (0 : ℝ) ≤ X := le_trans (by positivity) hX
  have hw := sector_xiSpectralSq_add n hX q
  have hne := xiSpectralSq_add_ofReal_ne_zero hX0 q
  have hnsq : 0 < Complex.normSq (xiSpectralPoint q ^ 2 + (X : ℂ)) :=
    Complex.normSq_pos.mpr hne
  rw [xiResolventPoint, Complex.inv_re, Complex.inv_im, abs_div, abs_neg,
    abs_of_pos hnsq, ← mul_div_assoc]
  exact div_lt_div_of_pos_right hw hnsq

/-! ## §3 Moment positivity to unbounded degree -/

/-- All resolvent-coordinate powers up to `n+1` have strictly positive real part at shift
`X ≥ ((2n+1)^2 + 1)/4`. -/
theorem xiResolventPoint_pow_re_pos {k n : ℕ} (hkn : k ≤ n) {X : ℝ}
    (hX : ((2 * (n : ℝ) + 1) ^ 2 + 1) / 4 ≤ X) (q : XiZeroCopy) :
    0 < ((xiResolventPoint X q) ^ (k + 1)).re := by
  have hthr : ((2 * (k : ℝ) + 1) ^ 2 + 1) / 4 ≤ X :=
    le_trans (resolventSector_threshold_mono hkn) hX
  exact re_pow_pos_of_sector _ k (sector_xiResolventPoint k hthr q)

/-- **Every resolvent moment is strictly positive at its quadratic shift threshold** — the
diagonal of the Hankel criterion holds unconditionally to unbounded degree. -/
theorem xiResolventMoment_re_pos (n : ℕ) {X : ℝ}
    (hX : ((2 * (n : ℝ) + 1) ^ 2 + 1) / 4 ≤ X) :
    0 < (xiResolventMoment n X).re := by
  have hX0 : (0 : ℝ) ≤ X := le_trans (by positivity) hX
  have hsum := summable_xiResolventPoint_pow hX0 n
  rw [xiResolventMoment, Complex.re_tsum hsum]
  have hre : Summable (fun q : XiZeroCopy => (xiResolventPoint X q ^ (n + 1)).re) :=
    (Complex.hasSum_re hsum.hasSum).summable
  obtain ⟨q₀⟩ := nonempty_xiZeroCopy
  exact hre.tsum_pos (fun q => (xiResolventPoint_pow_re_pos le_rfl hX q).le) q₀
    (xiResolventPoint_pow_re_pos le_rfl hX q₀)

/-- Clean threshold form: the `n`-th moment is strictly positive once `X ≥ (n+1)^2`. -/
theorem xiResolventMoment_re_pos_of_add_one_sq_le (n : ℕ) {X : ℝ}
    (hX : ((n : ℝ) + 1) ^ 2 ≤ X) : 0 < (xiResolventMoment n X).re := by
  refine xiResolventMoment_re_pos n (le_trans ?_ hX)
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

/-! ## §4 Unconditional Hankel positivity on the nonnegative cone -/

/-- The real part of the Hankel form is the weighted double sum of moment real parts. -/
theorem xiResolventHankelForm_re (N : ℕ) (a : ℕ → ℝ) (X : ℝ) :
    (xiResolventHankelForm N a X).re =
      ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
        a j * a k * (xiResolventMoment (j + k) X).re := by
  rw [xiResolventHankelForm, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]

/-- **Unconditional Hankel nonnegativity on the nonnegative-coefficient cone** at shift
`X ≥ ((4N+1)^2 + 1)/4`: every moment appearing in the form is strictly positive there. -/
theorem xiResolventHankelForm_re_nonneg_of_nonneg (N : ℕ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j) {X : ℝ}
    (hX : ((2 * ((2 * N : ℕ) : ℝ) + 1) ^ 2 + 1) / 4 ≤ X) :
    0 ≤ (xiResolventHankelForm N a X).re := by
  rw [xiResolventHankelForm_re]
  refine Finset.sum_nonneg fun j hj => Finset.sum_nonneg fun k hk => ?_
  have hjk : j + k ≤ 2 * N := by
    have h1 := Finset.mem_range.mp hj
    have h2 := Finset.mem_range.mp hk
    omega
  have hmom := xiResolventMoment_re_pos (j + k)
    (le_trans (resolventSector_threshold_mono hjk) hX)
  exact mul_nonneg (mul_nonneg (ha j) (ha k)) hmom.le

/-- **Strict Hankel positivity on the nonnegative cone**: a single strictly positive coefficient
below the truncation order forces a strictly positive form. -/
theorem xiResolventHankelForm_re_pos_of_nonneg (N : ℕ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j) {i : ℕ} (hi : i < N) (hai : 0 < a i) {X : ℝ}
    (hX : ((2 * ((2 * N : ℕ) : ℝ) + 1) ^ 2 + 1) / 4 ≤ X) :
    0 < (xiResolventHankelForm N a X).re := by
  have hmom : ∀ {m : ℕ}, m ≤ 2 * N → 0 < (xiResolventMoment m X).re := fun {m} hm =>
    xiResolventMoment_re_pos m (le_trans (resolventSector_threshold_mono hm) hX)
  have hterm : ∀ j ∈ Finset.range N, (0 : ℝ) ≤
      ∑ k ∈ Finset.range N, a j * a k * (xiResolventMoment (j + k) X).re := by
    intro j hj
    refine Finset.sum_nonneg fun k hk => ?_
    have h1 := Finset.mem_range.mp hj
    have h2 := Finset.mem_range.mp hk
    exact mul_nonneg (mul_nonneg (ha j) (ha k)) (hmom (by omega)).le
  rw [xiResolventHankelForm_re]
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum hterm (Finset.mem_range.mpr hi))
  have hinner : ∀ k ∈ Finset.range N, (0 : ℝ) ≤
      a i * a k * (xiResolventMoment (i + k) X).re := by
    intro k hk
    have h2 := Finset.mem_range.mp hk
    exact mul_nonneg (mul_nonneg (ha i) (ha k)) (hmom (by omega)).le
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum hinner (Finset.mem_range.mpr hi))
  exact mul_pos (mul_pos hai hai) (hmom (by omega))

/-- Clean threshold form: the nonnegative cone is unconditionally Hankel-nonnegative once
`X ≥ (2N+1)^2`. -/
theorem xiResolventHankelForm_re_nonneg_of_nonneg_of_sq_le (N : ℕ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j) {X : ℝ} (hX : (2 * (N : ℝ) + 1) ^ 2 ≤ X) :
    0 ≤ (xiResolventHankelForm N a X).re := by
  refine xiResolventHankelForm_re_nonneg_of_nonneg N a ha (le_trans ?_ hX)
  push_cast
  nlinarith [Nat.cast_nonneg (α := ℝ) N]

/-- **Any Hankel negativity witness at admissible shift has sign-changing coefficients.**  The
form is even in the weight, so a one-signed weight of either sign is covered by the cone
positivity; a negative value forces coefficients of both strict signs. -/
theorem exists_coeff_neg_and_pos_of_xiResolventHankelForm_re_neg (N : ℕ) (a : ℕ → ℝ)
    {X : ℝ} (hX : ((2 * ((2 * N : ℕ) : ℝ) + 1) ^ 2 + 1) / 4 ≤ X)
    (hneg : (xiResolventHankelForm N a X).re < 0) :
    (∃ j, a j < 0) ∧ (∃ k, 0 < a k) := by
  constructor
  · by_contra h
    simp only [not_exists, not_lt] at h
    exact absurd (xiResolventHankelForm_re_nonneg_of_nonneg N a h hX)
      (not_le.mpr hneg)
  · by_contra h
    simp only [not_exists, not_lt] at h
    have hform : xiResolventHankelForm N a X =
        xiResolventHankelForm N (fun j => -a j) X := by
      rw [xiResolventHankelForm, xiResolventHankelForm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      push_cast
      ring
    have hnn : ∀ j, 0 ≤ -a j := fun j => neg_nonneg.mpr (h j)
    rw [hform] at hneg
    exact absurd (xiResolventHankelForm_re_nonneg_of_nonneg N _ hnn hX)
      (not_le.mpr hneg)

end

end RHTower
