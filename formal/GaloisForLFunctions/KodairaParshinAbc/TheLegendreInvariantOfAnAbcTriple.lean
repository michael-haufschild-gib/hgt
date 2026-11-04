import GaloisForLFunctions.HTGeometry.LegendreHalfCoordinates
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaModularInvariant

/-!
# The Legendre invariant of an `abc` triple

For `a + b = c` the Legendre curve `y² = x(x-1)(x-λ)` with `λ = a/c` (the Frey curve of the
triple) has modular invariant

  `j = 256 (a² + ab + b²)³ / (abc)² = 32 (a² + b² + c²)³ / (abc)²`,

so `j` is a function of the triple invariant under the six substitutions
`λ ↦ λ, 1-λ, 1/λ, 1/(1-λ), 1-1/λ, λ/(λ-1)`, i.e. under all permutations of `(a, b, -c)`.

Over `ℤ`, for a primitive triple the numerator `256 (a²+ab+b²)³` and the denominator `(abc)²`
share at most the factor `256`, because `a² + ab + b²` is prime to `a`, `b` and `a + b`.
Hence the naive height of `j` is comparable to `H⁶`, `H = max(|a|,|b|,|c|)`, from both sides:

  `H⁶ ≤ 8 H(j)`  and  `H(j) ≤ 864 H⁶`.

The upper bound is the degree-six comparison `H(f(P)) ≪ H(P)⁶` for the map
`f(x₀,x₁,x₂) = (256 (x₀² + x₁x₂)³, (x₀x₁x₂)²)` at `P = (λ, 1-λ, 1)`; the lower bound is its
reverse on primitive integral points.
-/

noncomputable section

namespace GaloisForLFunctions.KodairaParshinAbc

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica (legendreJ)

/-! ## The modular invariant of the Legendre curve -/

section Curve

variable {F : Type*} [Field F] [CharZero F]

omit [CharZero F] in
theorem legendre_c₄ (lam : F) :
    WeierstrassCurve.c₄ (LegendreDoubling.curve lam) = 16 * (lam ^ 2 - lam + 1) := by
  simp only [LegendreDoubling.curve, WeierstrassCurve.c₄, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄]
  ring

omit [CharZero F] in
theorem legendre_Δ (lam : F) :
    WeierstrassCurve.Δ (LegendreDoubling.curve lam) = 16 * lam ^ 2 * (lam - 1) ^ 2 := by
  simp only [LegendreDoubling.curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

/-- The Legendre curve is elliptic exactly off the three degenerate parameters `0, 1, ∞`. -/
theorem legendre_isElliptic_iff (lam : F) :
    WeierstrassCurve.IsElliptic (LegendreDoubling.curve lam) ↔ lam ≠ 0 ∧ lam ≠ 1 := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero, legendre_Δ]
  constructor
  · intro h
    refine ⟨fun h0 => h (by simp [h0]), fun h1 => h (by simp [h1])⟩
  · rintro ⟨h0, h1⟩
    have h1' : lam - 1 ≠ 0 := sub_ne_zero.mpr h1
    exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 h0)) (pow_ne_zero 2 h1')

theorem legendre_ne_zero_ne_one (lam : F)
    [WeierstrassCurve.IsElliptic (LegendreDoubling.curve lam)] : lam ≠ 0 ∧ lam ≠ 1 :=
  (legendre_isElliptic_iff lam).mp inferInstance

/-- **The Legendre `j`-invariant**: `j(y² = x(x-1)(x-λ)) = 256 (λ²-λ+1)³ / (λ²(λ-1)²)`. -/
theorem legendre_j (lam : F) [WeierstrassCurve.IsElliptic (LegendreDoubling.curve lam)] :
    WeierstrassCurve.j (LegendreDoubling.curve lam) =
      256 * (lam ^ 2 - lam + 1) ^ 3 / (lam ^ 2 * (lam - 1) ^ 2) := by
  obtain ⟨h0, h1⟩ := legendre_ne_zero_ne_one lam
  have h1' : lam - 1 ≠ 0 := sub_ne_zero.mpr h1
  rw [WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ', legendre_Δ,
    legendre_c₄]
  field_simp
  ring

/-- **The Frey–Legendre invariant of an `abc` triple.**  For `a + b = c` with `abc ≠ 0`, the
Legendre curve with parameter `a/c` has `j = 256 (a² + ab + b²)³ / (abc)²`. -/
theorem legendre_j_abc {a b c : F} (hab : a + b = c) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    [WeierstrassCurve.IsElliptic (LegendreDoubling.curve (a / c))] :
    WeierstrassCurve.j (LegendreDoubling.curve (a / c)) =
      256 * (a ^ 2 + a * b + b ^ 2) ^ 3 / (a * b * c) ^ 2 := by
  have hl1 : a / c - 1 = -b / c := by field_simp; linear_combination hab
  rw [legendre_j, hl1]
  subst hab
  field_simp
  ring

/-- The Legendre curve of a triple with `abc ≠ 0` is elliptic. -/
theorem legendre_isElliptic_abc {a b c : F} (hab : a + b = c) (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : c ≠ 0) : WeierstrassCurve.IsElliptic (LegendreDoubling.curve (a / c)) := by
  rw [legendre_isElliptic_iff]
  refine ⟨div_ne_zero ha hc, fun h => hb ?_⟩
  rw [div_eq_one_iff_eq hc] at h
  subst hab
  linear_combination -h

end Curve

/-! ## The real Legendre invariant and its `S₃`-orbit -/

/-- The modular invariant of the corpus Legendre curve over `ℝ` is the real Legendre invariant
`legendreJ`. -/
theorem legendre_j_eq_legendreJ (m : ℝ)
    [WeierstrassCurve.IsElliptic (LegendreDoubling.curve m)] :
    WeierstrassCurve.j (LegendreDoubling.curve m) = legendreJ m := by
  rw [legendre_j, legendreJ]
  congr 1 <;> ring

/-- `legendreJ` is invariant under `λ ↦ 1/λ` (with the junk values at `0` and `1` matching). -/
theorem legendreJ_inv (m : ℝ) : legendreJ m⁻¹ = legendreJ m := by
  by_cases h0 : m = 0
  · simp [h0]
  by_cases h1 : m = 1
  · simp [h1]
  have h1' : m - 1 ≠ 0 := sub_ne_zero.mpr h1
  have h1'' : 1 - m ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  rw [legendreJ, legendreJ]
  field_simp
  ring

/-- **The anharmonic orbit.**  All six parameters `λ, 1-λ, 1/λ, 1/(1-λ), 1-1/λ, 1/(1-1/λ)`
have the same Legendre invariant. -/
theorem legendreJ_orbit (m : ℝ) :
    legendreJ (1 - m) = legendreJ m ∧ legendreJ m⁻¹ = legendreJ m ∧
      legendreJ (1 - m)⁻¹ = legendreJ m ∧ legendreJ (1 - m⁻¹) = legendreJ m ∧
        legendreJ (1 - m⁻¹)⁻¹ = legendreJ m := by
  refine ⟨DispersivePDE.BrizardElastica.legendreJ_one_sub m, legendreJ_inv m, ?_, ?_, ?_⟩
  · rw [legendreJ_inv, DispersivePDE.BrizardElastica.legendreJ_one_sub]
  · rw [DispersivePDE.BrizardElastica.legendreJ_one_sub, legendreJ_inv]
  · rw [legendreJ_inv, DispersivePDE.BrizardElastica.legendreJ_one_sub, legendreJ_inv]

/-- **The symmetric form.**  For `a + b = c` with `abc ≠ 0`,
`legendreJ (a/c) = 32 (a² + b² + c²)³ / (abc)²`. -/
theorem legendreJ_div_abc {a b c : ℝ} (hab : a + b = c) (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : c ≠ 0) :
    legendreJ (a / c) = 32 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 3 / (a * b * c) ^ 2 := by
  have hl1 : 1 - a / c = b / c := by field_simp; linear_combination -hab
  rw [legendreJ, hl1]
  subst hab
  field_simp
  ring

/-! ## Integral triples: the numerator and denominator of `j` -/

/-- `a² + ab + b²` is prime to each of `a`, `b`, `a + b` when `a, b` are coprime. -/
theorem isCoprime_abcQuadratic {a b : ℤ} (h : IsCoprime a b) :
    IsCoprime (a ^ 2 + a * b + b ^ 2) (a * b * (a + b)) := by
  have h1 : IsCoprime (a ^ 2 + a * b + b ^ 2) a := by
    have := (h.symm.pow_left (m := 2)).add_mul_left_left (a + b)
    rwa [show b ^ 2 + a * (a + b) = a ^ 2 + a * b + b ^ 2 by ring] at this
  have h2 : IsCoprime (a ^ 2 + a * b + b ^ 2) b := by
    have := (h.pow_left (m := 2)).add_mul_left_left (a + b)
    rwa [show a ^ 2 + b * (a + b) = a ^ 2 + a * b + b ^ 2 by ring] at this
  have h3 : IsCoprime (a ^ 2 + a * b + b ^ 2) (a + b) := by
    have hb : IsCoprime b (a + b) := by
      have := h.symm.add_mul_left_right 1
      simpa [add_comm] using this
    have := (hb.pow_left (m := 2)).add_mul_left_left a
    rwa [show b ^ 2 + (a + b) * a = a ^ 2 + a * b + b ^ 2 by ring] at this
  exact (h1.mul_right h2).mul_right h3

/-- The numerator and denominator of `j = 256 (a²+ab+b²)³/(abc)²` share at most `256`. -/
theorem gcd_abcInvariant_dvd {a b : ℤ} (h : IsCoprime a b) :
    (Int.gcd (256 * (a ^ 2 + a * b + b ^ 2) ^ 3) ((a * b * (a + b)) ^ 2) : ℤ) ∣ 256 := by
  obtain ⟨u, v, huv⟩ := (isCoprime_abcQuadratic h).pow (m := 3) (n := 2)
  have h1 := Int.gcd_dvd_left (256 * (a ^ 2 + a * b + b ^ 2) ^ 3) ((a * b * (a + b)) ^ 2)
  have h2 := Int.gcd_dvd_right (256 * (a ^ 2 + a * b + b ^ 2) ^ 3) ((a * b * (a + b)) ^ 2)
  have key : (256 : ℤ) = u * (256 * (a ^ 2 + a * b + b ^ 2) ^ 3) +
      (256 * v) * (a * b * (a + b)) ^ 2 := by
    linear_combination (-256 : ℤ) * huv
  have := dvd_add (dvd_mul_of_dvd_right h1 u) (dvd_mul_of_dvd_right h2 (256 * v))
  rwa [← key] at this

/-- The height `max(|a|, |b|, |a+b|)` of the triple `(a, b, a + b)`. -/
def tripleHeight (a b : ℤ) : ℤ := max |a| (max |b| |a + b|)

theorem abs_le_tripleHeight (a b : ℤ) :
    |a| ≤ tripleHeight a b ∧ |b| ≤ tripleHeight a b ∧ |a + b| ≤ tripleHeight a b :=
  ⟨le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
    (le_max_right _ _).trans (le_max_right _ _)⟩

theorem tripleHeight_mem (a b : ℤ) :
    tripleHeight a b = |a| ∨ tripleHeight a b = |b| ∨ tripleHeight a b = |a + b| := by
  unfold tripleHeight
  rcases max_choice |a| (max |b| |a + b|) with h | h
  · exact Or.inl h
  · rw [h]
    rcases max_choice |b| |a + b| with h' | h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr h')

/-- `2 (a² + ab + b²) = a² + b² + (a+b)²` lies between `H²` and `3 H²`. -/
theorem tripleHeight_sq_bounds (a b : ℤ) :
    tripleHeight a b ^ 2 ≤ 2 * (a ^ 2 + a * b + b ^ 2) ∧
      2 * (a ^ 2 + a * b + b ^ 2) ≤ 3 * tripleHeight a b ^ 2 := by
  obtain ⟨ha, hb, hc⟩ := abs_le_tripleHeight a b
  have hsa : a ^ 2 ≤ tripleHeight a b ^ 2 := by
    rw [← sq_abs a]; exact pow_le_pow_left₀ (abs_nonneg a) ha 2
  have hsb : b ^ 2 ≤ tripleHeight a b ^ 2 := by
    rw [← sq_abs b]; exact pow_le_pow_left₀ (abs_nonneg b) hb 2
  have hsc : (a + b) ^ 2 ≤ tripleHeight a b ^ 2 := by
    rw [← sq_abs (a + b)]; exact pow_le_pow_left₀ (abs_nonneg _) hc 2
  have hsum : 2 * (a ^ 2 + a * b + b ^ 2) = a ^ 2 + b ^ 2 + (a + b) ^ 2 := by ring
  refine ⟨?_, by rw [hsum]; linarith⟩
  rw [hsum]
  rcases tripleHeight_mem a b with h | h | h <;> rw [h, sq_abs] <;> nlinarith [sq_nonneg a,
    sq_nonneg b, sq_nonneg (a + b)]

/-- **Degree-six comparison for the numerator**: `32 H⁶ ≤ 256 (a²+ab+b²)³ ≤ 864 H⁶`. -/
theorem abcInvariant_num_bounds (a b : ℤ) :
    32 * tripleHeight a b ^ 6 ≤ 256 * (a ^ 2 + a * b + b ^ 2) ^ 3 ∧
      256 * (a ^ 2 + a * b + b ^ 2) ^ 3 ≤ 864 * tripleHeight a b ^ 6 := by
  obtain ⟨hlo, hhi⟩ := tripleHeight_sq_bounds a b
  have h0 : 0 ≤ tripleHeight a b ^ 2 := sq_nonneg _
  have hlo3 := pow_le_pow_left₀ h0 hlo 3
  have hhi3 := pow_le_pow_left₀ (h0.trans hlo) hhi 3
  constructor <;> nlinarith [hlo3, hhi3]

/-- **Degree-six comparison for the denominator**: `(ab(a+b))² ≤ H⁶`. -/
theorem abcInvariant_den_le (a b : ℤ) : (a * b * (a + b)) ^ 2 ≤ tripleHeight a b ^ 6 := by
  obtain ⟨ha, hb, hc⟩ := abs_le_tripleHeight a b
  have h : |a * b * (a + b)| ≤ tripleHeight a b ^ 3 := by
    rw [abs_mul, abs_mul, pow_three]
    have h0 : 0 ≤ tripleHeight a b := (abs_nonneg a).trans ha
    exact mul_le_mul (mul_le_mul ha hb (abs_nonneg _) h0) hc (abs_nonneg _)
      (mul_nonneg h0 h0) |>.trans_eq (by ring)
  calc (a * b * (a + b)) ^ 2 = |a * b * (a + b)| ^ 2 := (sq_abs _).symm
    _ ≤ (tripleHeight a b ^ 3) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
    _ = tripleHeight a b ^ 6 := by ring

/-! ## The naive height of `j` -/

/-- The naive height `max(|num q|, den q)` of a rational number. -/
def ratHeight (q : ℚ) : ℕ := max q.num.natAbs q.den

/-- For `q = n/d` with `d ≠ 0`, reducing the fraction cancels a common factor of `n` and `d`;
if `gcd(n, d)` divides `g > 0`, then `|n| ≤ g |num q|` and `|d| ≤ g · den q`. -/
theorem abs_le_of_div {n d : ℤ} (hd : d ≠ 0) {g : ℤ} (hg : (Int.gcd n d : ℤ) ∣ g) (hg0 : 0 < g) :
    |n| ≤ g * |((n : ℚ) / d).num| ∧ |d| ≤ g * (((n : ℚ) / d).den : ℤ) := by
  set q : ℚ := (n : ℚ) / d with hq
  have hden : (q.den : ℤ) ∣ d := by
    have := Rat.den_dvd n d
    rwa [Rat.divInt_eq_div] at this
  obtain ⟨e, he⟩ := hden
  have hden0 : (q.den : ℤ) ≠ 0 := by exact_mod_cast q.den_nz
  have hrel : n * (q.den : ℤ) = q.num * d := by
    have h1 : q * q.den = q.num := Rat.mul_den_eq_num q
    have h2 : (q : ℚ) * d = n := by rw [hq]; field_simp
    have : ((n * (q.den : ℤ) : ℤ) : ℚ) = ((q.num * d : ℤ) : ℚ) := by
      push_cast
      rw [← h2, ← h1]
      ring
    exact_mod_cast this
  have hn : n = q.num * e := by
    rw [he] at hrel
    have : (q.den : ℤ) * (n - q.num * e) = 0 := by linear_combination hrel
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hden0
    · linear_combination h
  have he_dvd : e ∣ (Int.gcd n d : ℤ) :=
    Int.dvd_coe_gcd (hn ▸ dvd_mul_left e q.num) (he ▸ dvd_mul_left e (q.den : ℤ))
  have he_le : |e| ≤ g :=
    Int.le_of_dvd hg0 ((abs_dvd e g).mpr (he_dvd.trans hg))
  refine ⟨?_, ?_⟩
  · rw [hn, abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right he_le (abs_nonneg _)
  · rw [he, abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ q.den), mul_comm]
    exact mul_le_mul_of_nonneg_right he_le (by positivity)

/-- **The height of the Frey–Legendre invariant is `≍ H⁶`.**  For coprime `a, b` with
`ab(a+b) ≠ 0`, the rational number `j = 256 (a²+ab+b²)³/(ab(a+b))²` satisfies
`H⁶ ≤ 8 H(j)` and `H(j) ≤ 864 H⁶`, where `H = max(|a|, |b|, |a+b|)`. -/
theorem ratHeight_abcInvariant_bounds {a b : ℤ} (h : IsCoprime a b) (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : a + b ≠ 0) :
    tripleHeight a b ^ 6 ≤ 8 * (ratHeight (((256 * (a ^ 2 + a * b + b ^ 2) ^ 3 : ℤ) : ℚ) /
        (((a * b * (a + b)) ^ 2 : ℤ) : ℚ)) : ℤ) ∧
      (ratHeight (((256 * (a ^ 2 + a * b + b ^ 2) ^ 3 : ℤ) : ℚ) /
        (((a * b * (a + b)) ^ 2 : ℤ) : ℚ)) : ℤ) ≤ 864 * tripleHeight a b ^ 6 := by
  set n : ℤ := 256 * (a ^ 2 + a * b + b ^ 2) ^ 3 with hn
  set d : ℤ := (a * b * (a + b)) ^ 2 with hd
  have hd0 : d ≠ 0 := pow_ne_zero 2 (mul_ne_zero (mul_ne_zero ha hb) hc)
  obtain ⟨hnlo, hnhi⟩ := abcInvariant_num_bounds a b
  have hdhi := abcInvariant_den_le a b
  have hd_pos : 0 < d := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hd0)
  have hq0 : 0 ≤ a ^ 2 + a * b + b ^ 2 := by nlinarith [sq_nonneg (a + b), sq_nonneg a, sq_nonneg b]
  have hn_pos : 0 ≤ n := by rw [hn]; positivity
  set q : ℚ := (n : ℚ) / d with hq
  have hcast : (ratHeight q : ℤ) = max |q.num| (q.den : ℤ) := by
    simp [ratHeight]
  -- Upper bound: the reduced numerator and denominator divide `n` and `d`.
  have hnum_le : |q.num| ≤ |n| := by
    by_cases hn0 : n = 0
    · have : q = 0 := by rw [hq, hn0]; simp
      rw [this, hn0]; simp
    have hdvd : q.num ∣ n := by
      have := Rat.num_dvd n hd0
      rwa [Rat.divInt_eq_div] at this
    exact Int.le_of_dvd (abs_pos.mpr hn0) ((abs_dvd_abs _ _).mpr hdvd)
  have hden_le : (q.den : ℤ) ≤ d := by
    have hdvd : (q.den : ℤ) ∣ d := by
      have := Rat.den_dvd n d
      rwa [Rat.divInt_eq_div] at this
    exact Int.le_of_dvd hd_pos hdvd
  -- Lower bound: the cancelled factor divides `gcd(n, d) ∣ 256`.
  obtain ⟨hn_le, hd_le⟩ := abs_le_of_div hd0 (gcd_abcInvariant_dvd h) (by norm_num)
  have hH0 : 0 ≤ tripleHeight a b := (abs_nonneg a).trans (abs_le_tripleHeight a b).1
  refine ⟨?_, ?_⟩
  · rw [hcast]
    have : |n| ≤ 256 * max |q.num| (q.den : ℤ) :=
      hn_le.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num))
    rw [abs_of_nonneg hn_pos] at this
    linarith
  · rw [hcast]
    refine max_le (hnum_le.trans ?_) (hden_le.trans ?_)
    · rw [abs_of_nonneg hn_pos]; exact hnhi
    · nlinarith [pow_nonneg hH0 6]

end GaloisForLFunctions.KodairaParshinAbc
