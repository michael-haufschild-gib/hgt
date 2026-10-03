import GaloisForLFunctions.HTGeometry.StonehamParityDrift

/-!
# Phase sums along the orbit of `4` modulo `3ᵏ`

For `q = 3ᵏ`, `τ = 3^{k−1}` and `b ≡ 2 (mod 3)`, the points `ρₓ = b 4ˣ mod q` run through the
residue class `2 mod 3`, and `uₓ = ⌊ρₓ/3⌋` through `[0, τ)`.  The twisted complete sums

`S(η, β) = Σ_{x<τ} e((η uₓ + β x)/τ)`

satisfy `|S|² ≤ τ · #{z < τ : τ ∣ η(4ᶻ − 1)}`, which is at most `τ 3ʲ` when `3ʲ ∤ η`.
Completing incomplete sums over `x < m` costs a factor `2 + log τ`; together with the
geometric bound for interval sums this gives a discrepancy bound for `{uₓ : x < m}` against
thresholds:

`|#{x < m : c ≤ uₓ} − m(τ − c)/τ| ≤ (1 + log τ)((2 + log τ) √(τ 3ʲ) + τ/3ʲ)`.
-/

open Finset Filter Topology

namespace GaloisForLFunctions.HTGeometry.StonehamParityDrift

/-! ### The phase `e_M(n) = exp(2πi n/M)` -/

/-- `e_M(n) = exp(2πi n/M)`. -/
noncomputable def ephase (M : ℕ) (n : ℤ) : ℂ :=
  Complex.exp (((2 * Real.pi * ((n : ℝ) / M) : ℝ) : ℂ) * Complex.I)

theorem norm_ephase (M : ℕ) (n : ℤ) : ‖ephase M n‖ = 1 := Complex.norm_exp_ofReal_mul_I _

theorem ephase_add (M : ℕ) (a b : ℤ) : ephase M (a + b) = ephase M a * ephase M b := by
  unfold ephase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem ephase_zero (M : ℕ) : ephase M 0 = 1 := by simp [ephase]

theorem ephase_mul_self {M : ℕ} (hM : M ≠ 0) (t : ℤ) : ephase M (M * t) = 1 := by
  unfold ephase
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM
  have : ((2 * Real.pi * (((M * t : ℤ) : ℝ) / M) : ℝ) : ℂ) * Complex.I =
      (t : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    field_simp
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

theorem ephase_congr {M : ℕ} (hM : M ≠ 0) {a b : ℤ} (h : a ≡ b [ZMOD M]) :
    ephase M a = ephase M b := by
  obtain ⟨t, ht⟩ := h.dvd
  rw [show b = a + M * t by linarith, ephase_add, ephase_mul_self hM, mul_one]

theorem ephase_neg (M : ℕ) (n : ℤ) : ephase M (-n) = starRingEnd ℂ (ephase M n) := by
  unfold ephase
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  simp only [Int.cast_neg, neg_div, mul_neg, Complex.ofReal_neg, neg_mul, mul_neg]

theorem ephase_three_mul {M : ℕ} (hM : M ≠ 0) (n : ℤ) : ephase (3 * M) (3 * n) = ephase M n := by
  unfold ephase
  congr 3
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM
  push_cast
  field_simp

theorem ephase_mul_nat (M : ℕ) (a : ℤ) (n : ℕ) : ephase M (a * n) = ephase M a ^ n := by
  unfold ephase
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem ephase_ne_one {M : ℕ} (hM : M ≠ 0) {a : ℤ} (ha : ¬ (M : ℤ) ∣ a) : ephase M a ≠ 1 := by
  intro h
  unfold ephase at h
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM
  have hre : 2 * Real.pi * ((a : ℝ) / M) = n * (2 * Real.pi) := by
    have := congrArg Complex.im hn
    simpa using this
  have : (a : ℝ) = M * n := by
    have hpi := Real.pi_pos
    field_simp at hre
    nlinarith
  exact ha ⟨n, by exact_mod_cast this⟩

/-- Orthogonality: `Σ_{u<M} e_M(a u) = M [M ∣ a]`. -/
theorem sum_ephase_range {M : ℕ} (hM : M ≠ 0) (a : ℤ) :
    ∑ u ∈ range M, ephase M (a * u) = if (M : ℤ) ∣ a then (M : ℂ) else 0 := by
  split_ifs with h
  · obtain ⟨t, rfl⟩ := h
    rw [sum_congr rfl fun u _ => by rw [mul_assoc, ephase_mul_self hM]]
    simp
  · simp_rw [ephase_mul_nat]
    rw [geom_sum_eq (ephase_ne_one hM h), ← ephase_mul_nat, mul_comm, ephase_mul_self hM,
      sub_self, zero_div]

theorem norm_ephase_sub_one (M : ℕ) (a : ℤ) :
    ‖ephase M a - 1‖ = 2 * |Real.sin (Real.pi * a / M)| := by
  unfold ephase
  rw [mul_comm, Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_two]
  congr 2
  ring_nf

/-- **Interval sums.**  `‖Σ_{s ∈ [c, d)} e_M(a s)‖ ≤ 1/|sin(πa/M)|` when `M ∤ a`. -/
theorem norm_sum_Ico_ephase_le {M : ℕ} (hM : M ≠ 0) {a : ℤ} (ha : ¬ (M : ℤ) ∣ a) (c d : ℕ) :
    ‖∑ s ∈ Ico c d, ephase M (a * s)‖ ≤ 1 / |Real.sin (Real.pi * a / M)| := by
  set z := ephase M a with hz
  have hz1 : z ≠ 1 := ephase_ne_one hM ha
  have hsin : 0 < |Real.sin (Real.pi * a / M)| := by
    have h1 : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz1)
    rw [hz, norm_ephase_sub_one] at h1
    linarith
  have hnz : ‖z‖ = 1 := norm_ephase M a
  simp_rw [ephase_mul_nat]
  rcases le_or_gt d c with hdc | hcd
  · rw [Ico_eq_empty_of_le hdc, sum_empty, norm_zero]; positivity
  rw [sum_Ico_eq_sum_range, ← hz]
  simp_rw [pow_add]
  rw [← mul_sum, geom_sum_eq hz1, norm_mul, norm_pow, hnz, one_pow, one_mul, norm_div,
    hz, norm_ephase_sub_one, ← hz]
  have h2 : ‖z ^ (d - c) - 1‖ ≤ 2 := by
    calc ‖z ^ (d - c) - 1‖ ≤ ‖z ^ (d - c)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hnz, one_pow, norm_one]; norm_num
  rw [div_le_div_iff₀ (by positivity) hsin]
  nlinarith

/-- `sin(πη/M) ≥ 2 min(η, M − η)/M` for `0 < η < M`. -/
theorem two_mul_min_div_le_sin {M η : ℕ} (hη : 0 < η) (hηM : η < M) :
    2 * (min η (M - η) : ℕ) / (M : ℝ) ≤ Real.sin (Real.pi * η / M) := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  rcases le_total (2 * η) M with h | h
  · rw [min_eq_left (by omega)]
    have hx0 : 0 ≤ Real.pi * η / M := by positivity
    have hx1 : Real.pi * η / M ≤ Real.pi / 2 := by
      rw [div_le_div_iff₀ hMpos (by norm_num)]
      have : (2 * η : ℝ) ≤ M := by exact_mod_cast h
      nlinarith [Real.pi_pos]
    have := Real.mul_le_sin hx0 hx1
    calc 2 * (η : ℝ) / M = 2 / Real.pi * (Real.pi * η / M) := by
          field_simp
      _ ≤ _ := this
  · rw [min_eq_right (by omega)]
    have hx0 : 0 ≤ Real.pi * ((M - η : ℕ) : ℝ) / M := by positivity
    have hx1 : Real.pi * ((M - η : ℕ) : ℝ) / M ≤ Real.pi / 2 := by
      rw [div_le_div_iff₀ hMpos (by norm_num)]
      have : (2 * (M - η : ℕ) : ℝ) ≤ M := by exact_mod_cast (show 2 * (M - η) ≤ M by omega)
      nlinarith [Real.pi_pos]
    have := Real.mul_le_sin hx0 hx1
    have hrefl : Real.sin (Real.pi * η / M) = Real.sin (Real.pi * ((M - η : ℕ) : ℝ) / M) := by
      rw [← Real.sin_pi_sub]
      congr 1
      push_cast [hηM.le]
      field_simp
    rw [hrefl]
    calc 2 * ((M - η : ℕ) : ℝ) / M = 2 / Real.pi * (Real.pi * ((M - η : ℕ) : ℝ) / M) := by
          field_simp
      _ ≤ _ := this

theorem sin_pos_of_lt {M η : ℕ} (hη : 0 < η) (hηM : η < M) :
    0 < Real.sin (Real.pi * η / M) := by
  refine lt_of_lt_of_le ?_ (two_mul_min_div_le_sin hη hηM)
  have : 0 < min η (M - η) := by omega
  have hM : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  positivity

/-- `Σ_{0<η<M} 1/sin(πη/M) ≤ M (1 + log M)`. -/
theorem sum_inv_sin_le (M : ℕ) :
    ∑ η ∈ Ioo 0 M, 1 / Real.sin (Real.pi * η / M) ≤ M * (1 + Real.log M) := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hterm : ∀ η ∈ Ioo 0 M, 1 / Real.sin (Real.pi * η / M) ≤
      (M : ℝ) / 2 * (1 / (η : ℝ) + 1 / ((M - η : ℕ) : ℝ)) := by
    intro η hη
    rw [mem_Ioo] at hη
    have hs := two_mul_min_div_le_sin hη.1 hη.2
    have hmin : 0 < min η (M - η) := by omega
    have hminr : (0 : ℝ) < (min η (M - η) : ℕ) := by exact_mod_cast hmin
    have hη0 : (0 : ℝ) < η := by exact_mod_cast hη.1
    have hMη : (0 : ℝ) < ((M - η : ℕ) : ℝ) := by exact_mod_cast (show 0 < M - η by omega)
    calc 1 / Real.sin (Real.pi * η / M) ≤ 1 / (2 * (min η (M - η) : ℕ) / (M : ℝ)) :=
          one_div_le_one_div_of_le (by positivity) hs
      _ = (M : ℝ) / 2 * (1 / ((min η (M - η) : ℕ) : ℝ)) := by field_simp
      _ ≤ (M : ℝ) / 2 * (1 / (η : ℝ) + 1 / ((M - η : ℕ) : ℝ)) := by
          gcongr
          rcases le_total η (M - η) with h | h
          · rw [min_eq_left h]; have : (0 : ℝ) ≤ 1 / ((M - η : ℕ) : ℝ) := by positivity
            linarith
          · rw [min_eq_right h]; have : (0 : ℝ) ≤ 1 / (η : ℝ) := by positivity
            linarith
  have hIoo : Ioo 0 M = Icc 1 (M - 1) := by ext x; simp only [mem_Ioo, mem_Icc]; omega
  have hH : ∑ η ∈ Ioo 0 M, 1 / (η : ℝ) = (harmonic (M - 1) : ℝ) := by
    rw [harmonic_eq_sum_Icc, hIoo]; push_cast; simp
  have hrefl : ∑ η ∈ Ioo 0 M, 1 / ((M - η : ℕ) : ℝ) = ∑ η ∈ Ioo 0 M, 1 / (η : ℝ) := by
    refine sum_nbij' (fun η => M - η) (fun η => M - η) ?_ ?_ ?_ ?_ ?_ <;>
      intro η hη <;> simp only [mem_Ioo] at hη ⊢ <;> omega
  calc ∑ η ∈ Ioo 0 M, 1 / Real.sin (Real.pi * η / M)
      ≤ ∑ η ∈ Ioo 0 M, (M : ℝ) / 2 * (1 / (η : ℝ) + 1 / ((M - η : ℕ) : ℝ)) := sum_le_sum hterm
    _ = (M : ℝ) * (harmonic (M - 1) : ℝ) := by
        rw [← mul_sum, sum_add_distrib, hrefl, hH]; ring
    _ ≤ M * (1 + Real.log M) := by
        gcongr
        refine (harmonic_le_one_add_log (M - 1)).trans ?_
        have hlog : Real.log ((M - 1 : ℕ) : ℝ) ≤ Real.log M := by
          rcases Nat.eq_zero_or_pos (M - 1) with h0 | h0
          · rw [h0, Nat.cast_zero, Real.log_zero]
            exact Real.log_nonneg (by exact_mod_cast hM)
          · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast Nat.sub_le M 1)
        linarith

/-! ### The orbit of `4` on the class `2 mod 3` -/

/-- The orbit point `ρₓ = b 4ˣ mod 3ᵏ`. -/
def orbitPt (k b x : ℕ) : ℕ := b * 4 ^ x % 3 ^ k

/-- The class coordinate `uₓ = ⌊ρₓ/3⌋`. -/
def orbitCoord (k b x : ℕ) : ℕ := orbitPt k b x / 3

theorem three_pow_eq_three_mul {k : ℕ} (hk : 1 ≤ k) : 3 ^ k = 3 * 3 ^ (k - 1) := by
  rw [← pow_succ']; congr 1; omega

theorem orbitPt_mod_three {k b : ℕ} (hk : 1 ≤ k) (hb : b % 3 = 2) (x : ℕ) :
    orbitPt k b x % 3 = 2 := by
  unfold orbitPt
  rw [Nat.mod_mod_of_dvd _ (dvd_pow_self 3 (by omega)), Nat.mul_mod, Nat.pow_mod]
  norm_num [hb]

theorem orbitPt_eq {k b : ℕ} (hk : 1 ≤ k) (hb : b % 3 = 2) (x : ℕ) :
    orbitPt k b x = 3 * orbitCoord k b x + 2 := by
  have := Nat.div_add_mod (orbitPt k b x) 3
  rw [orbitPt_mod_three hk hb] at this
  unfold orbitCoord; omega

theorem orbitCoord_lt {k : ℕ} (hk : 1 ≤ k) (b x : ℕ) : orbitCoord k b x < 3 ^ (k - 1) := by
  unfold orbitCoord orbitPt
  have h := Nat.mod_lt (b * 4 ^ x) (show 0 < 3 ^ k by positivity)
  have hq := three_pow_eq_three_mul hk
  omega

theorem orbitPt_add_mul_period {k : ℕ} (hk : 1 ≤ k) (b x n : ℕ) :
    orbitPt k b (x + 3 ^ (k - 1) * n) = orbitPt k b x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [mul_add, mul_one, ← add_assoc]
    have h1 := three_pow_dvd_four_pow_sub_one hk
    have hmod : 4 ^ 3 ^ (k - 1) % 3 ^ k = 1 % 3 ^ k :=
      ((Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).mpr h1).symm
    unfold orbitPt at ih ⊢
    rw [pow_add, ← mul_assoc, Nat.mul_mod, hmod, ← Nat.mul_mod, mul_one, ih]

theorem orbitPt_mod_period {k : ℕ} (hk : 1 ≤ k) (b x : ℕ) :
    orbitPt k b (x % 3 ^ (k - 1)) = orbitPt k b x := by
  conv_rhs => rw [← Nat.mod_add_div x (3 ^ (k - 1))]
  rw [orbitPt_add_mul_period hk]

theorem orbitPt_add_modEq (k b y z : ℕ) :
    (orbitPt k b (y + z) : ℤ) ≡ 4 ^ z * orbitPt k b y [ZMOD (3 ^ k : ℕ)] := by
  unfold orbitPt
  push_cast
  calc ((b : ℤ) * 4 ^ (y + z)) % 3 ^ k ≡ b * 4 ^ (y + z) [ZMOD 3 ^ k] := Int.mod_modEq _ _
    _ = 4 ^ z * (b * 4 ^ y) := by ring
    _ ≡ 4 ^ z * ((b * 4 ^ y) % 3 ^ k) [ZMOD 3 ^ k] := ((Int.mod_modEq _ _).symm).mul_left _

/-! ### The complete twisted sum -/

/-- `S(η, β) = Σ_{x<τ} e_τ(η uₓ + β x)`, `τ = 3^{k−1}`. -/
noncomputable def twistedSum (k b η β : ℕ) : ℂ :=
  ∑ x ∈ range (3 ^ (k - 1)), ephase (3 ^ (k - 1)) (η * orbitCoord k b x + β * x)

/-- The class `2 mod 3` below `3ᵏ` is the image of `u ↦ 3u + 2`. -/
theorem sum_residueClass_two {k : ℕ} (hk : 1 ≤ k) {M : Type*} [AddCommMonoid M] (F : ℕ → M) :
    ∑ r ∈ residueClass k 2, F r = ∑ u ∈ range (3 ^ (k - 1)), F (3 * u + 2) := by
  have hq := three_pow_eq_three_mul hk
  refine (sum_nbij' (fun u => 3 * u + 2) (fun r => r / 3) ?_ ?_ ?_ ?_ ?_).symm
  · intro u hu; simp only [residueClass, mem_filter, mem_range] at hu ⊢; omega
  · intro r hr; simp only [residueClass, mem_filter, mem_range] at hr ⊢; omega
  · intro u _; omega
  · intro r hr; simp only [residueClass, mem_filter, mem_range] at hr; omega
  · intro u _; rfl

/-- The inner orbit sum: `Σ_{y<τ} e_q(A ρ_y) = e_q(2A) τ [τ ∣ A]`. -/
theorem sum_ephase_orbitPt {k b : ℕ} (hk : 1 ≤ k) (hb : b % 3 = 2) (A : ℤ) :
    ∑ y ∈ range (3 ^ (k - 1)), ephase (3 ^ k) (A * orbitPt k b y) =
      ephase (3 ^ k) (2 * A) *
        if ((3 ^ (k - 1) : ℕ) : ℤ) ∣ A then ((3 ^ (k - 1) : ℕ) : ℂ) else 0 := by
  have hb3 : ¬ 3 ∣ b := by omega
  have hτ : 3 ^ (k - 1) ≠ 0 := by positivity
  have hq := three_pow_eq_three_mul hk
  unfold orbitPt
  rw [sum_range_orbit_eq hk hb3 (fun r => ephase (3 ^ k) (A * r)), hb,
    sum_residueClass_two hk, ← sum_ephase_range hτ A, mul_sum]
  refine sum_congr rfl fun u _ => ?_
  rw [show ephase (3 ^ (k - 1)) (A * u) = ephase (3 ^ k) (3 * (A * u)) by
    rw [hq, ephase_three_mul hτ], ← ephase_add]
  congr 1
  push_cast
  ring

/-- The phase of a pair `(x, y)` with `x ≡ y + z (mod τ)`. -/
theorem ephase_pair {k b : ℕ} (hk : 1 ≤ k) (hb : b % 3 = 2) (η β y z : ℕ) :
    ephase (3 ^ (k - 1)) ((η : ℤ) * orbitCoord k b ((y + z) % 3 ^ (k - 1)) +
        (β : ℤ) * (((y + z) % 3 ^ (k - 1) : ℕ) : ℤ) - ((η : ℤ) * orbitCoord k b y + β * y)) =
      ephase (3 ^ k) (((η : ℤ) * (4 ^ z - 1)) * orbitPt k b y) * ephase (3 ^ (k - 1)) (β * z) := by
  have hτ : 3 ^ (k - 1) ≠ 0 := by positivity
  have hq := three_pow_eq_three_mul hk
  have hq0 : 3 ^ k ≠ 0 := by positivity
  have hper : orbitPt k b ((y + z) % 3 ^ (k - 1)) = orbitPt k b (y + z) :=
    orbitPt_mod_period hk b _
  have hcoord : (3 : ℤ) * (orbitCoord k b ((y + z) % 3 ^ (k - 1)) - orbitCoord k b y : ℤ) =
      orbitPt k b (y + z) - orbitPt k b y := by
    rw [← hper, orbitPt_eq hk hb ((y + z) % 3 ^ (k - 1)), orbitPt_eq hk hb y]; push_cast; ring
  rw [show (η : ℤ) * orbitCoord k b ((y + z) % 3 ^ (k - 1)) +
      β * (((y + z) % 3 ^ (k - 1) : ℕ) : ℤ) - (η * orbitCoord k b y + β * y) =
      η * (orbitCoord k b ((y + z) % 3 ^ (k - 1)) - orbitCoord k b y : ℤ) +
        β * ((((y + z) % 3 ^ (k - 1) : ℕ) : ℤ) - y) by ring, ephase_add]
  congr 1
  · rw [← ephase_three_mul hτ, ← hq,
      show (3 : ℤ) * (η * (orbitCoord k b ((y + z) % 3 ^ (k - 1)) - orbitCoord k b y : ℤ)) =
        η * (3 * (orbitCoord k b ((y + z) % 3 ^ (k - 1)) - orbitCoord k b y : ℤ)) by ring,
      hcoord]
    apply ephase_congr hq0
    have h := orbitPt_add_modEq k b y z
    calc (η : ℤ) * ((orbitPt k b (y + z) : ℤ) - orbitPt k b y)
        ≡ η * (4 ^ z * orbitPt k b y - orbitPt k b y) [ZMOD (3 ^ k : ℕ)] :=
          (h.sub_right _).mul_left _
      _ = η * (4 ^ z - 1) * orbitPt k b y := by ring
  · apply ephase_congr hτ
    apply Int.ModEq.mul_left
    rw [Int.modEq_iff_dvd]
    refine ⟨((y + z) / 3 ^ (k - 1) : ℕ), ?_⟩
    have := Nat.mod_add_div (y + z) (3 ^ (k - 1))
    have h' : ((y + z : ℕ) : ℤ) = (((y + z) % 3 ^ (k - 1) : ℕ) : ℤ) +
        ((3 ^ (k - 1) : ℕ) : ℤ) * (((y + z) / 3 ^ (k - 1) : ℕ) : ℤ) := by
      exact_mod_cast this.symm
    push_cast at h' ⊢
    linarith

/-- Reindexing a sum over `range τ` by `x = (y + z) mod τ`. -/
theorem sum_range_mod_shift {τ y : ℕ} (hy : y < τ) {M : Type*} [AddCommMonoid M] (F : ℕ → M) :
    ∑ x ∈ range τ, F x = ∑ z ∈ range τ, F ((y + z) % τ) := by
  have hτpos : 0 < τ := by omega
  refine (sum_nbij' (fun z => (y + z) % τ) (fun x => (x + τ - y) % τ) ?_ ?_ ?_ ?_ ?_).symm
  · intro z _; exact mem_range.mpr (Nat.mod_lt _ hτpos)
  · intro x _; exact mem_range.mpr (Nat.mod_lt _ hτpos)
  · intro z hz
    rw [mem_range] at hz
    rcases lt_or_ge (y + z) τ with h | h
    · rw [Nat.mod_eq_of_lt h, show y + z + τ - y = z + τ by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt hz]
    · rw [show (y + z) % τ = y + z - τ by
        rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)],
        show y + z - τ + τ - y = z by omega, Nat.mod_eq_of_lt hz]
  · intro x hx
    rw [mem_range] at hx
    rcases lt_or_ge (x + τ - y) τ with h | h
    · rw [Nat.mod_eq_of_lt h, show y + (x + τ - y) = x + τ by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt hx]
    · rw [show (x + τ - y) % τ = x - y by
        rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]; omega,
        show y + (x - y) = x by omega, Nat.mod_eq_of_lt hx]
  · intro z _; rfl

/-- **Complete sum bound.**  `‖S(η, β)‖² ≤ τ · #{z < τ : τ ∣ η(4ᶻ − 1)}`. -/
theorem norm_twistedSum_sq_le {k b : ℕ} (hk : 1 ≤ k) (hb : b % 3 = 2) (η β : ℕ) :
    ‖twistedSum k b η β‖ ^ 2 ≤
      3 ^ (k - 1) * #{z ∈ range (3 ^ (k - 1)) | 3 ^ (k - 1) ∣ η * (4 ^ z - 1)} := by
  have hexp : ((‖twistedSum k b η β‖ ^ 2 : ℝ) : ℂ) = ∑ z ∈ range (3 ^ (k - 1)),
      ephase (3 ^ (k - 1)) (β * z) * ∑ y ∈ range (3 ^ (k - 1)),
        ephase (3 ^ k) (((η : ℤ) * (4 ^ z - 1)) * orbitPt k b y) := by
    push_cast
    rw [← Complex.ofReal_pow, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, twistedSum,
      map_sum, sum_mul_sum, sum_comm]
    simp_rw [← ephase_neg, ← ephase_add, ← sub_eq_add_neg, mul_sum]
    conv_rhs => rw [sum_comm]
    refine sum_congr rfl fun y hy => ?_
    rw [sum_range_mod_shift (mem_range.mp hy)]
    refine sum_congr rfl fun z _ => ?_
    rw [ephase_pair hk hb]
    ring
  have hinner : ∀ z ∈ range (3 ^ (k - 1)),
      ‖ephase (3 ^ (k - 1)) (β * z) * ∑ y ∈ range (3 ^ (k - 1)),
        ephase (3 ^ k) (((η : ℤ) * (4 ^ z - 1)) * orbitPt k b y)‖ ≤
        if 3 ^ (k - 1) ∣ η * (4 ^ z - 1) then ((3 ^ (k - 1) : ℕ) : ℝ) else 0 := by
    intro z _
    rw [norm_mul, norm_ephase, one_mul, sum_ephase_orbitPt hk hb, norm_mul, norm_ephase, one_mul]
    have hcast : ((η : ℤ) * (4 ^ z - 1)) = ((η * (4 ^ z - 1) : ℕ) : ℤ) := by
      rw [Nat.cast_mul, Nat.cast_sub (Nat.one_le_pow _ _ (by norm_num))]; push_cast; ring
    simp only [hcast, Int.natCast_dvd_natCast]
    split_ifs <;> simp
  have hreal : ‖twistedSum k b η β‖ ^ 2 = ‖((‖twistedSum k b η β‖ ^ 2 : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [hreal, hexp]
  refine (norm_sum_le _ _).trans ((sum_le_sum hinner).trans ?_)
  rw [← sum_filter, sum_const, nsmul_eq_mul]
  exact le_of_eq (by push_cast; ring)

/-- Only multiples of `3^{k−1−j}` satisfy `τ ∣ η(4ᶻ − 1)` when `3ʲ ∤ η`, so there are at most
`3ʲ` of them. -/
theorem card_filter_dvd_le {k j η : ℕ} (hjk : j + 1 ≤ k) (hη : ¬ 3 ^ j ∣ η) :
    #{z ∈ range (3 ^ (k - 1)) | 3 ^ (k - 1) ∣ η * (4 ^ z - 1)} ≤ 3 ^ j := by
  have hη0 : η ≠ 0 := by rintro rfl; exact hη (dvd_zero _)
  have hvη : padicValNat 3 η < j := by
    by_contra h
    exact hη ((padicValNat_dvd_iff_le hη0).mpr (not_lt.mp h))
  have hsub : {z ∈ range (3 ^ (k - 1)) | 3 ^ (k - 1) ∣ η * (4 ^ z - 1)} ⊆
      {z ∈ range (3 ^ (k - 1)) | 3 ^ (k - 1 - j) ∣ z} := by
    intro z hz
    simp only [mem_filter, mem_range] at hz ⊢
    refine ⟨hz.1, ?_⟩
    rcases Nat.eq_zero_or_pos z with rfl | hz0
    · exact dvd_zero _
    have h4 : 4 ^ z - 1 ≠ 0 := by
      have := Nat.one_lt_pow hz0.ne' (by norm_num : 1 < 4); omega
    have hv := (padicValNat_dvd_iff_le (mul_ne_zero hη0 h4)).mp hz.2
    rw [padicValNat.mul hη0 h4, padicValNat_four_pow_sub_one hz0.ne'] at hv
    exact (pow_dvd_pow 3 (by omega)).trans pow_padicValNat_dvd
  refine (card_le_card hsub).trans ?_
  have hsplit : 3 ^ (k - 1) = 3 ^ (k - 1 - j) * 3 ^ j := by rw [← pow_add]; congr 1; omega
  have hd : 0 < 3 ^ (k - 1 - j) := by positivity
  calc #{z ∈ range (3 ^ (k - 1)) | 3 ^ (k - 1 - j) ∣ z} ≤ #(range (3 ^ j)) := by
        refine card_le_card_of_injOn (fun z => z / 3 ^ (k - 1 - j)) ?_ ?_
        · intro z hz
          simp only [coe_filter, mem_range, Set.mem_setOf_eq, coe_range, Set.mem_Iio] at hz ⊢
          rw [Nat.div_lt_iff_lt_mul hd, mul_comm, ← hsplit]
          exact hz.1
        · intro z1 hz1 z2 hz2 h
          simp only [coe_filter, mem_range, Set.mem_setOf_eq] at hz1 hz2 h
          rw [← Nat.div_mul_cancel hz1.2, ← Nat.div_mul_cancel hz2.2, h]
    _ = 3 ^ j := card_range _

theorem norm_twistedSum_le {k b j : ℕ} (hk : 1 ≤ k) (hb : b % 3 = 2) (hjk : j + 1 ≤ k) {η : ℕ}
    (hη : ¬ 3 ^ j ∣ η) (β : ℕ) :
    ‖twistedSum k b η β‖ ≤ Real.sqrt (3 ^ (k - 1) * 3 ^ j) := by
  rw [Real.le_sqrt (norm_nonneg _) (by positivity)]
  refine (norm_twistedSum_sq_le hk hb η β).trans ?_
  gcongr
  exact_mod_cast card_filter_dvd_le hjk hη

/-! ### Completion of incomplete orbit sums -/

/-- `T(η, m) = Σ_{x<m} e_τ(η uₓ)`. -/
noncomputable def orbitPhaseSum (k b η m : ℕ) : ℂ :=
  ∑ x ∈ range m, ephase (3 ^ (k - 1)) (η * orbitCoord k b x)

theorem sum_range_eq_add_sum_Ioo {M : ℕ} (hM : 0 < M) {R : Type*} [AddCommMonoid R]
    (f : ℕ → R) : ∑ β ∈ range M, f β = f 0 + ∑ β ∈ Ioo 0 M, f β := by
  have : range M = insert 0 (Ioo 0 M) := by
    ext x; simp only [mem_range, mem_insert, mem_Ioo]; omega
  rw [this, sum_insert (by simp)]

/-- `Σ_{β<M} ‖Σ_{y<m} e_M(−β y)‖ ≤ M (2 + log M)` for `m ≤ M`. -/
theorem sum_norm_geom_le {M m : ℕ} (hM : 0 < M) (hm : m ≤ M) :
    ∑ β ∈ range M, ‖∑ y ∈ range m, ephase M (-(β : ℤ) * y)‖ ≤ M * (2 + Real.log M) := by
  rw [sum_range_eq_add_sum_Ioo hM]
  have h0 : ‖∑ y ∈ range m, ephase M (-((0 : ℕ) : ℤ) * y)‖ ≤ M := by
    refine (norm_sum_le _ _).trans ?_
    simp only [norm_ephase, sum_const, card_range, nsmul_eq_mul, mul_one]
    exact_mod_cast hm
  have hβ : ∀ β ∈ Ioo 0 M, ‖∑ y ∈ range m, ephase M (-(β : ℤ) * y)‖ ≤
      1 / Real.sin (Real.pi * β / M) := by
    intro β hβ
    rw [mem_Ioo] at hβ
    have hndvd : ¬ (M : ℤ) ∣ -(β : ℤ) := by
      rw [Int.dvd_neg, Int.natCast_dvd_natCast]
      exact Nat.not_dvd_of_pos_of_lt hβ.1 hβ.2
    have := norm_sum_Ico_ephase_le hM.ne' hndvd 0 m
    rw [← range_eq_Ico] at this
    refine this.trans (le_of_eq ?_)
    push_cast
    rw [mul_neg, neg_div, Real.sin_neg, abs_neg, abs_of_pos (sin_pos_of_lt hβ.1 hβ.2)]
  have := sum_inv_sin_le M
  calc _ ≤ (M : ℝ) + ∑ β ∈ Ioo 0 M, 1 / Real.sin (Real.pi * β / M) :=
        add_le_add h0 (sum_le_sum hβ)
    _ ≤ M * (2 + Real.log M) := by linarith

/-- **Completion.**  For `m ≤ τ`, `T(η, m) = τ⁻¹ Σ_{β<τ} S(η, β) Σ_{y<m} e_τ(−β y)`. -/
theorem orbitPhaseSum_eq_completion {k b : ℕ} (η : ℕ) {m : ℕ} (hm : m ≤ 3 ^ (k - 1)) :
    orbitPhaseSum k b η m = (1 / (3 ^ (k - 1) : ℕ)) * ∑ β ∈ range (3 ^ (k - 1)),
      twistedSum k b η β * ∑ y ∈ range m, ephase (3 ^ (k - 1)) (-(β : ℤ) * y) := by
  have hτ : 3 ^ (k - 1) ≠ 0 := by positivity
  have hτc : ((3 ^ (k - 1) : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hτ
  have hterm : ∀ β x y : ℕ, ephase (3 ^ (k - 1)) (η * orbitCoord k b x + β * x) *
      ephase (3 ^ (k - 1)) (-(β : ℤ) * y) = ephase (3 ^ (k - 1)) (η * orbitCoord k b x) *
        ephase (3 ^ (k - 1)) (((x : ℤ) - y) * β) := by
    intro β x y
    rw [← ephase_add, ← ephase_add]
    congr 1
    ring
  have hrhs : ∑ β ∈ range (3 ^ (k - 1)), twistedSum k b η β *
      ∑ y ∈ range m, ephase (3 ^ (k - 1)) (-(β : ℤ) * y) =
      ∑ x ∈ range (3 ^ (k - 1)), ∑ y ∈ range m, ephase (3 ^ (k - 1)) (η * orbitCoord k b x) *
        if ((3 ^ (k - 1) : ℕ) : ℤ) ∣ ((x : ℤ) - y) then ((3 ^ (k - 1) : ℕ) : ℂ) else 0 := by
    simp_rw [twistedSum, sum_mul_sum, hterm]
    rw [sum_comm]
    refine sum_congr rfl fun x _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun y _ => ?_
    rw [← mul_sum, ← sum_ephase_range hτ]
  rw [hrhs, sum_comm]
  rw [orbitPhaseSum, mul_sum]
  refine sum_congr rfl fun y hy => ?_
  have hy' : y < 3 ^ (k - 1) := lt_of_lt_of_le (mem_range.mp hy) hm
  rw [sum_eq_single y]
  · rw [if_pos (by simp)]
    field_simp
  · intro x hx hxy
    rw [if_neg, mul_zero]
    rintro ⟨t, ht⟩
    have hx' : (x : ℤ) < 3 ^ (k - 1) := by exact_mod_cast mem_range.mp hx
    have hy'' : (y : ℤ) < 3 ^ (k - 1) := by exact_mod_cast hy'
    have hpos : (0 : ℤ) < 3 ^ (k - 1) := by positivity
    push_cast at ht
    have ht0 : t = 0 := by
      rcases lt_trichotomy t 0 with h | h | h
      · have : t ≤ -1 := by omega
        nlinarith
      · exact h
      · have : 1 ≤ t := by omega
        nlinarith
    rw [ht0, mul_zero] at ht
    exact hxy (by omega)
  · intro h; exact absurd (mem_range.mpr hy') h

/-- **Incomplete orbit sums.**  If `3ʲ ∤ η` and `m ≤ τ`, then
`‖T(η, m)‖ ≤ (2 + log τ) √(τ 3ʲ)`. -/
theorem norm_orbitPhaseSum_le {k b j : ℕ} (hk : 1 ≤ k) (hb : b % 3 = 2) (hjk : j + 1 ≤ k)
    {η : ℕ} (hη : ¬ 3 ^ j ∣ η) {m : ℕ} (hm : m ≤ 3 ^ (k - 1)) :
    ‖orbitPhaseSum k b η m‖ ≤ (2 + Real.log (3 ^ (k - 1))) * Real.sqrt (3 ^ (k - 1) * 3 ^ j) := by
  have hτ : (0 : ℝ) < 3 ^ (k - 1) := by positivity
  rw [orbitPhaseSum_eq_completion η hm, norm_mul]
  have hS := norm_twistedSum_le (k := k) hk hb hjk hη
  have hG := sum_norm_geom_le (M := 3 ^ (k - 1)) (by positivity) hm
  calc ‖(1 / ((3 ^ (k - 1) : ℕ) : ℂ))‖ * ‖∑ β ∈ range (3 ^ (k - 1)), twistedSum k b η β *
        ∑ y ∈ range m, ephase (3 ^ (k - 1)) (-(β : ℤ) * y)‖
      ≤ (1 / 3 ^ (k - 1)) * ∑ β ∈ range (3 ^ (k - 1)), Real.sqrt (3 ^ (k - 1) * 3 ^ j) *
          ‖∑ y ∈ range m, ephase (3 ^ (k - 1)) (-(β : ℤ) * y)‖ := by
        rw [norm_div, norm_one, Complex.norm_natCast]
        push_cast
        gcongr
        refine (norm_sum_le _ _).trans (sum_le_sum fun β _ => ?_)
        rw [norm_mul]
        gcongr
        exact hS β
    _ ≤ (1 / 3 ^ (k - 1)) * (Real.sqrt (3 ^ (k - 1) * 3 ^ j) *
          (3 ^ (k - 1) * (2 + Real.log (3 ^ (k - 1))))) := by
        rw [← mul_sum]
        gcongr
        push_cast at hG
        exact hG
    _ = (2 + Real.log (3 ^ (k - 1))) * Real.sqrt (3 ^ (k - 1) * 3 ^ j) := by
        field_simp

/-! ### Counting against thresholds -/

theorem int_dvd_sub_iff_eq {τ a s : ℕ} (ha : a < τ) (hs : s < τ) :
    (τ : ℤ) ∣ ((a : ℤ) - s) ↔ a = s := by
  constructor
  · rintro ⟨t, ht⟩
    have ha' : (a : ℤ) < τ := by exact_mod_cast ha
    have hs' : (s : ℤ) < τ := by exact_mod_cast hs
    have hpos : (0 : ℤ) < τ := by omega
    have ht0 : t = 0 := by
      rcases lt_trichotomy t 0 with h | h | h
      · have : t ≤ -1 := by omega
        nlinarith
      · exact h
      · have : 1 ≤ t := by omega
        nlinarith
    rw [ht0, mul_zero] at ht
    omega
  · rintro rfl; simp

theorem sum_Ico_ite_dvd {τ u c : ℕ} (hu : u < τ) :
    ∑ s ∈ Ico c τ, (if (τ : ℤ) ∣ ((u : ℤ) - s) then (τ : ℂ) else 0) =
      if c ≤ u then (τ : ℂ) else 0 := by
  by_cases h1 : c ≤ u
  · rw [if_pos h1, sum_eq_single_of_mem u (mem_Ico.mpr ⟨h1, hu⟩)]
    · simp
    · intro s hs hsu
      rw [if_neg]
      rw [int_dvd_sub_iff_eq hu (mem_Ico.mp hs).2]
      exact fun h => hsu h.symm
  · rw [if_neg h1]
    refine sum_eq_zero fun s hs => ?_
    rw [if_neg]
    rw [int_dvd_sub_iff_eq hu (mem_Ico.mp hs).2]
    intro h
    exact h1 (h ▸ (mem_Ico.mp hs).1)

/-- **Counting by orthogonality.** -/
theorem card_threshold_eq {k : ℕ} (hk : 1 ≤ k) (b c m : ℕ) :
    (#{x ∈ range m | c ≤ orbitCoord k b x} : ℂ) =
      (1 / (3 ^ (k - 1) : ℕ)) * ∑ η ∈ range (3 ^ (k - 1)),
        (∑ s ∈ Ico c (3 ^ (k - 1)), ephase (3 ^ (k - 1)) (-(η : ℤ) * s)) *
          orbitPhaseSum k b η m := by
  have hτ : 3 ^ (k - 1) ≠ 0 := by positivity
  have hτc : ((3 ^ (k - 1) : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hτ
  have hpt : ∀ x : ℕ, (if c ≤ orbitCoord k b x then (1 : ℂ) else 0) =
      (1 / (3 ^ (k - 1) : ℕ)) * ∑ s ∈ Ico c (3 ^ (k - 1)), ∑ η ∈ range (3 ^ (k - 1)),
        ephase (3 ^ (k - 1)) (((orbitCoord k b x : ℤ) - s) * η) := by
    intro x
    have hu := orbitCoord_lt hk b x
    simp_rw [sum_ephase_range hτ]
    rw [sum_Ico_ite_dvd hu]
    split_ifs
    · field_simp
    · rw [mul_zero]
  rw [card_filter, Nat.cast_sum]
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  simp only [hpt]
  rw [← mul_sum]
  congr 1
  simp_rw [orbitPhaseSum, sum_mul_sum, ← ephase_add]
  rw [sum_comm]
  conv_lhs => enter [2, s]; rw [sum_comm]
  rw [sum_comm]
  refine sum_congr rfl fun η _ => sum_congr rfl fun s _ => sum_congr rfl fun x _ => ?_
  congr 1
  ring

theorem sum_inv_sin_multiples_le (j n : ℕ) :
    ∑ η ∈ {η ∈ Ioo 0 (3 ^ j * n) | 3 ^ j ∣ η}, 1 / Real.sin (Real.pi * η / (3 ^ j * n : ℕ)) ≤
      n * (1 + Real.log n) := by
  have hpos : 0 < 3 ^ j := by positivity
  refine le_of_eq_of_le ?_ (sum_inv_sin_le n)
  refine (sum_nbij' (fun η => η / 3 ^ j) (fun η => 3 ^ j * η) ?_ ?_ ?_ ?_ ?_)
  · intro η hη
    rw [mem_filter, mem_Ioo] at hη
    rw [mem_Ioo]
    obtain ⟨⟨h1, h2⟩, t, rfl⟩ := hη
    rw [Nat.mul_div_cancel_left _ hpos]
    refine ⟨Nat.pos_of_ne_zero fun h => by simp [h] at h1, ?_⟩
    by_contra h
    have : 3 ^ j * n ≤ 3 ^ j * t := Nat.mul_le_mul_left _ (not_lt.mp h)
    omega
  · intro η hη
    rw [mem_Ioo] at hη
    rw [mem_filter, mem_Ioo]
    refine ⟨⟨Nat.mul_pos hpos hη.1, ?_⟩, dvd_mul_right _ _⟩
    have := Nat.mul_le_mul_left (3 ^ j) hη.2
    rw [Nat.mul_succ] at this
    omega
  · intro η hη
    rw [mem_filter] at hη
    exact Nat.mul_div_cancel' hη.2
  · intro η _; exact Nat.mul_div_cancel_left _ hpos
  · intro η hη
    rw [mem_filter] at hη
    obtain ⟨t, rfl⟩ := hη.2
    rw [Nat.mul_div_cancel_left _ hpos]
    congr 2
    have : (0 : ℝ) < 3 ^ j := by positivity
    push_cast
    field_simp

/-- **Threshold discrepancy of the orbit.**  For `j + 1 ≤ k`, `c ≤ τ` and `m ≤ τ`,
`|#{x < m : c ≤ uₓ} − m(τ − c)/τ| ≤ (1 + log τ)((2 + log τ) √(τ 3ʲ) + 3^{k−1−j})`. -/
theorem abs_card_threshold_sub_le {k b j : ℕ} (hk : 1 ≤ k) (hb : b % 3 = 2) (hjk : j + 1 ≤ k)
    {c m : ℕ} (hc : c ≤ 3 ^ (k - 1)) (hm : m ≤ 3 ^ (k - 1)) :
    |(#{x ∈ range m | c ≤ orbitCoord k b x} : ℝ) - m * (3 ^ (k - 1) - c) / 3 ^ (k - 1)| ≤
      (1 + Real.log (3 ^ (k - 1))) * ((2 + Real.log (3 ^ (k - 1))) *
        Real.sqrt (3 ^ (k - 1) * 3 ^ j) + 3 ^ (k - 1 - j)) := by
  have hcard := card_threshold_eq hk b c m
  have hTb : ∀ η, ¬ 3 ^ j ∣ η → ‖orbitPhaseSum k b η m‖ ≤
      (2 + Real.log (3 ^ (k - 1))) * Real.sqrt (3 ^ (k - 1) * 3 ^ j) :=
    fun η h => norm_orbitPhaseSum_le hk hb hjk h hm
  have hmult := sum_inv_sin_multiples_le j (3 ^ (k - 1 - j))
  have hsplit : 3 ^ j * 3 ^ (k - 1 - j) = 3 ^ (k - 1) := by rw [← pow_add]; congr 1; omega
  rw [hsplit] at hmult
  have hlog' : Real.log ((3 ^ (k - 1 - j) : ℕ) : ℝ) ≤ Real.log (3 ^ (k - 1)) := by
    push_cast
    exact Real.log_le_log (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega))
  have hτ' : ((3 ^ (k - 1 - j) : ℕ) : ℝ) = 3 ^ (k - 1 - j) := by push_cast; rfl
  obtain ⟨τ, hτdef⟩ : ∃ τ : ℕ, τ = 3 ^ (k - 1) := ⟨_, rfl⟩
  have hτR : ((τ : ℕ) : ℝ) = 3 ^ (k - 1) := by rw [hτdef]; push_cast; rfl
  rw [← hτdef] at hcard hc hm hmult
  rw [← hτR] at hTb hlog' ⊢
  rw [hτ'] at hmult hlog'
  have hτ0 : 0 < τ := by rw [hτdef]; positivity
  have hτr : (0 : ℝ) < τ := by exact_mod_cast hτ0
  have hlogτ : 0 ≤ Real.log (τ : ℝ) := Real.log_nonneg (by exact_mod_cast hτ0)
  set B : ℝ := (2 + Real.log τ) * Real.sqrt (τ * 3 ^ j) with hB
  have hB0 : 0 ≤ B := by positivity
  -- the frequency-zero term is the main term
  have hG0 : ∑ s ∈ Ico c τ, ephase τ (-((0 : ℕ) : ℤ) * s) = ((τ : ℝ) - c : ℝ) := by
    simp only [Nat.cast_zero, neg_zero, zero_mul, ephase_zero, sum_const, Nat.card_Ico,
      nsmul_eq_mul, mul_one]
    push_cast [hc]
    ring
  have hT0 : orbitPhaseSum k b 0 m = m := by simp [orbitPhaseSum, ephase_zero]
  have hdiff : (((#{x ∈ range m | c ≤ orbitCoord k b x} : ℝ) -
      m * ((τ : ℝ) - c) / τ : ℝ) : ℂ) = (1 / (τ : ℂ)) * ∑ η ∈ Ioo 0 τ,
        (∑ s ∈ Ico c τ, ephase τ (-(η : ℤ) * s)) * orbitPhaseSum k b η m := by
    rw [sum_range_eq_add_sum_Ioo hτ0, hG0, hT0, mul_add] at hcard
    push_cast at hcard ⊢
    rw [hcard]
    have : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ0.ne'
    field_simp
    ring
  have hG : ∀ η ∈ Ioo 0 τ, ‖∑ s ∈ Ico c τ, ephase τ (-(η : ℤ) * s)‖ ≤
      1 / Real.sin (Real.pi * η / τ) := by
    intro η hη
    rw [mem_Ioo] at hη
    have hndvd : ¬ (τ : ℤ) ∣ -(η : ℤ) := by
      rw [Int.dvd_neg, Int.natCast_dvd_natCast]
      exact Nat.not_dvd_of_pos_of_lt hη.1 hη.2
    refine (norm_sum_Ico_ephase_le hτ0.ne' hndvd c τ).trans (le_of_eq ?_)
    push_cast
    rw [mul_neg, neg_div, Real.sin_neg, abs_neg, abs_of_pos (sin_pos_of_lt hη.1 hη.2)]
  have hT : ∀ η ∈ Ioo 0 τ, ‖orbitPhaseSum k b η m‖ ≤ B + if 3 ^ j ∣ η then (τ : ℝ) else 0 := by
    intro η _
    split_ifs with h
    · have : ‖orbitPhaseSum k b η m‖ ≤ m := by
        refine (norm_sum_le _ _).trans ?_
        simp [norm_ephase]
      have hm' : (m : ℝ) ≤ τ := by exact_mod_cast hm
      linarith
    · rw [add_zero]
      exact hTb η h
  have hsin : ∀ η ∈ Ioo 0 τ, 0 ≤ 1 / Real.sin (Real.pi * η / τ) := fun η hη => by
    rw [mem_Ioo] at hη; exact (one_div_pos.mpr (sin_pos_of_lt hη.1 hη.2)).le
  have hmult' : ∑ η ∈ Ioo 0 τ, (1 / Real.sin (Real.pi * η / τ)) *
      (if 3 ^ j ∣ η then (τ : ℝ) else 0) ≤
      τ * (3 ^ (k - 1 - j) * (1 + Real.log τ)) := by
    simp_rw [mul_ite, mul_zero]
    rw [← sum_filter, ← sum_mul, mul_comm]
    gcongr
    refine hmult.trans ?_
    gcongr
  have habs : |(#{x ∈ range m | c ≤ orbitCoord k b x} : ℝ) - m * ((τ : ℝ) - c) / τ| =
      ‖(((#{x ∈ range m | c ≤ orbitCoord k b x} : ℝ) - m * ((τ : ℝ) - c) / τ : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  calc |(#{x ∈ range m | c ≤ orbitCoord k b x} : ℝ) - m * ((τ : ℝ) - c) / τ|
      = ‖(1 / (τ : ℂ)) * ∑ η ∈ Ioo 0 τ,
          (∑ s ∈ Ico c τ, ephase τ (-(η : ℤ) * s)) * orbitPhaseSum k b η m‖ := by
        rw [habs, hdiff]
    _ ≤ (1 / τ) * ∑ η ∈ Ioo 0 τ, (1 / Real.sin (Real.pi * η / τ)) *
          (B + if 3 ^ j ∣ η then (τ : ℝ) else 0) := by
        rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
        gcongr
        refine (norm_sum_le _ _).trans (sum_le_sum fun η hη => ?_)
        rw [norm_mul]
        exact mul_le_mul (hG η hη) (hT η hη) (norm_nonneg _) (hsin η hη)
    _ ≤ (1 / τ) * (B * (τ * (1 + Real.log τ)) + τ * (3 ^ (k - 1 - j) * (1 + Real.log τ))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have e : ∑ η ∈ Ioo 0 τ, (1 / Real.sin (Real.pi * η / τ)) *
            (B + if 3 ^ j ∣ η then (τ : ℝ) else 0) =
            B * ∑ η ∈ Ioo 0 τ, 1 / Real.sin (Real.pi * η / τ) + ∑ η ∈ Ioo 0 τ,
              (1 / Real.sin (Real.pi * η / τ)) * (if 3 ^ j ∣ η then (τ : ℝ) else 0) := by
          rw [mul_sum, ← sum_add_distrib]
          exact sum_congr rfl fun η _ => by ring
        rw [e]
        exact add_le_add (mul_le_mul_of_nonneg_left (sum_inv_sin_le τ) hB0) hmult'
    _ = (1 + Real.log τ) * (B + 3 ^ (k - 1 - j)) := by
        field_simp

end GaloisForLFunctions.HTGeometry.StonehamParityDrift
