import GaloisForLFunctions.HTGeometry.ToeplitzTotalPositivityOrderK

/-!
# The quadratic `1 + 2cos ψ · z + z²` is `PF_k` up to the Chebyshev threshold

The sequence `q = (1, 2cos ψ, 1, 0, 0, …)` is `PF_k` when `0 ≤ ψ` and `(k + 1)ψ ≤ π`
(`PFSeq.cosQuadratic`); so is `n ↦ rⁿ qₙ` for `r > 0` (`PFSeq.geom_mul`,
`PFSeq.cosQuadratic_geom`).

Proof.  Expand a Toeplitz minor with increasing rows `i` and columns `j` along its first row or
column; the sign of `d = j₀ − i₀` decides.  For `d < 0` the first column vanishes, and for `d > 2`
the first row vanishes.  For `d = 0` or `d = 2` the minor equals the minor of the tails.  For
`d = 1` it is `2cos ψ` times the tail minor when the next row or column is not adjacent.  When both
are adjacent, the two-term row expansion gives `D = 2cos ψ · D' − D''` (`det_of_succ_succ_row_two`).
Along a maximal run of adjacent `d = 1` steps of length `r` this is the Chebyshev recursion, so
`D = U_r(cos ψ) · X` with `X` a shorter minor.  Finally `U_r(cos ψ) = sin((r+1)ψ)/sin ψ ≥ 0` for
`(r + 1)ψ ≤ π` (`chebU_cos_nonneg`).
-/

open Finset Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Laplace expansion along a sparse first row or column -/

theorem det_of_succ_col_single {m : ℕ} (f : Fin (m + 1) → Fin (m + 1) → ℝ)
    (h : ∀ r : Fin m, f r.succ 0 = 0) :
    (Matrix.of f).det = f 0 0 * (Matrix.of fun r c : Fin m => f r.succ c.succ).det := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp only [Matrix.of_apply, h, mul_zero, zero_mul, Finset.sum_const_zero, add_zero,
    Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero]
  rfl

theorem det_of_succ_row_single {m : ℕ} (f : Fin (m + 1) → Fin (m + 1) → ℝ)
    (h : ∀ c : Fin m, f 0 c.succ = 0) :
    (Matrix.of f).det = f 0 0 * (Matrix.of fun r c : Fin m => f r.succ c.succ).det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp only [Matrix.of_apply, h, mul_zero, zero_mul, Finset.sum_const_zero, add_zero,
    Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero]
  rfl

/-- Two-term expansion along the first row, when the `(1,0)` cofactor is itself a single-column
expansion. -/
theorem det_of_succ_succ_row_two {m : ℕ} (f : Fin (m + 2) → Fin (m + 2) → ℝ)
    (h : ∀ c : Fin m, f 0 c.succ.succ = 0) (hcol : ∀ r : Fin m, f r.succ.succ 0 = 0) :
    (Matrix.of f).det = f 0 0 * (Matrix.of fun r c : Fin (m + 1) => f r.succ c.succ).det -
      f 0 1 * f 1 0 * (Matrix.of fun r c : Fin m => f r.succ.succ c.succ.succ).det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Matrix.of_apply, h, mul_zero, zero_mul, Finset.sum_const_zero, add_zero,
    Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero, Fin.val_succ]
  have hM01 : ((Matrix.of f).submatrix Fin.succ (Fin.succ (0 : Fin (m + 1))).succAbove).det =
      f 1 0 * (Matrix.of fun r c : Fin m => f r.succ.succ c.succ.succ).det := by
    have hsub : (Matrix.of f).submatrix Fin.succ (Fin.succ (0 : Fin (m + 1))).succAbove =
        Matrix.of fun r c : Fin (m + 1) => f r.succ ((1 : Fin (m + 2)).succAbove c) := by
      ext r c
      simp [Fin.succ_zero_eq_one]
    rw [hsub, det_of_succ_col_single _ (fun r => by
      simp only [Fin.one_succAbove_zero]; exact hcol r)]
    simp only [Fin.one_succAbove_zero, Fin.one_succAbove_succ, Fin.succ_zero_eq_one]
  rw [hM01]
  have h1 : (Fin.succ (0 : Fin (m + 1))) = 1 := Fin.succ_zero_eq_one
  simp only [h1]
  have : ((Matrix.of f).submatrix Fin.succ Fin.succ) =
      Matrix.of fun r c : Fin (m + 1) => f r.succ c.succ := rfl
  rw [this]
  norm_num
  ring

/-! ## Chebyshev values -/

/-- `U_n(x)`: `U₀ = 1`, `U₁ = 2x`, `U_{n+2} = 2x U_{n+1} − U_n`. -/
def chebU (x : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => 2 * x
  | n + 2 => 2 * x * chebU x (n + 1) - chebU x n

theorem chebU_succ_succ (x : ℝ) (n : ℕ) :
    chebU x (n + 2) = 2 * x * chebU x (n + 1) - chebU x n := rfl

theorem chebU_cos_mul_sin (ψ : ℝ) (n : ℕ) :
    chebU (Real.cos ψ) n * Real.sin ψ = Real.sin ((n + 1) * ψ) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp [chebU]
    | 1 =>
      simp only [chebU]
      rw [show ((1 : ℕ) + 1 : ℝ) * ψ = 2 * ψ by push_cast; ring, Real.sin_two_mul]
      ring
    | n + 2 =>
      rw [chebU_succ_succ, sub_mul, mul_assoc, ih (n + 1) (by omega), ih n (by omega)]
      have h1 := Real.sin_add (((n + 2 : ℕ) : ℝ) * ψ) ψ
      have h2 := Real.sin_sub (((n + 2 : ℕ) : ℝ) * ψ) ψ
      push_cast at h1 h2 ⊢
      rw [show ((n : ℝ) + 2 + 1) * ψ = (n + 2) * ψ + ψ by ring, h1,
        show ((n : ℝ) + 1) * ψ = (n + 2) * ψ - ψ by ring, h2,
        show ((n : ℝ) + 1 + 1) * ψ = (n + 2) * ψ by ring]
      ring

theorem chebU_one (n : ℕ) : chebU 1 n = n + 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp [chebU]
    | 1 => norm_num [chebU]
    | n + 2 =>
      rw [chebU_succ_succ, ih (n + 1) (by omega), ih n (by omega)]
      push_cast
      ring

/-- `U_n(cos ψ) ≥ 0` for `0 ≤ ψ`, `(n + 1)ψ ≤ π`. -/
theorem chebU_cos_nonneg {ψ : ℝ} (h0 : 0 ≤ ψ) {n : ℕ} (hn : ((n : ℝ) + 1) * ψ ≤ Real.pi) :
    0 ≤ chebU (Real.cos ψ) n := by
  rcases eq_or_lt_of_le h0 with hψ | hψ
  · rw [← hψ, Real.cos_zero, chebU_one]; positivity
  · rcases Nat.eq_zero_or_pos n with rfl | hnpos
    · simp [chebU]
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
      have hψπ : ψ < Real.pi := by nlinarith [Real.pi_pos]
      have hs : 0 < Real.sin ψ := Real.sin_pos_of_pos_of_lt_pi hψ hψπ
      have hs' : 0 ≤ Real.sin ((n + 1) * ψ) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) hn
      have := chebU_cos_mul_sin ψ n
      by_contra hneg
      push Not at hneg
      nlinarith

/-! ## The quadratic sequence -/

/-- The sequence `1, 2cos ψ, 1, 0, 0, …`. -/
def cosQuad (ψ : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 1 else if n = 1 then 2 * Real.cos ψ else if n = 2 then 1 else 0

theorem zext_cosQuad_of_neg (ψ : ℝ) {z : ℤ} (hz : z < 0) : zext (cosQuad ψ) z = 0 :=
  zext_of_neg _ hz

theorem zext_cosQuad_of_gt (ψ : ℝ) {z : ℤ} (hz : 2 < z) : zext (cosQuad ψ) z = 0 := by
  unfold zext cosQuad
  rw [if_pos (by omega)]
  have h0 : z.toNat ≠ 0 := by omega
  have h1 : z.toNat ≠ 1 := by omega
  have h2 : z.toNat ≠ 2 := by omega
  simp [h0, h1, h2]

theorem zext_cosQuad_zero (ψ : ℝ) : zext (cosQuad ψ) 0 = 1 := by
  simp [zext, cosQuad]

theorem zext_cosQuad_one (ψ : ℝ) : zext (cosQuad ψ) 1 = 2 * Real.cos ψ := by
  simp [zext, cosQuad]

theorem zext_cosQuad_two (ψ : ℝ) : zext (cosQuad ψ) 2 = 1 := by
  simp [zext, cosQuad]

/-- The Toeplitz minor with rows `i 0, …, i (m−1)` and columns `j 0, …, j (m−1)`. -/
def seqMinor (a : ℕ → ℝ) (m : ℕ) (i j : ℕ → ℕ) : ℝ :=
  (Matrix.of fun r c : Fin m => zext a ((j c : ℤ) - i r)).det

theorem seqMinor_zero (a : ℕ → ℝ) (i j : ℕ → ℕ) : seqMinor a 0 i j = 1 := by
  simp [seqMinor, Matrix.det_isEmpty]

theorem seqMinor_succ_of_col (a : ℕ → ℝ) (m : ℕ) (i j : ℕ → ℕ)
    (h : ∀ r : ℕ, 1 ≤ r → r ≤ m → zext a ((j 0 : ℤ) - i r) = 0) :
    seqMinor a (m + 1) i j =
      zext a ((j 0 : ℤ) - i 0) * seqMinor a m (fun l => i (l + 1)) (fun l => j (l + 1)) := by
  unfold seqMinor
  rw [det_of_succ_col_single _ (fun r => by
    simp only [Fin.val_succ, Fin.val_zero]
    exact h _ (by omega) (by omega))]
  simp [Fin.val_succ]

theorem seqMinor_succ_of_row (a : ℕ → ℝ) (m : ℕ) (i j : ℕ → ℕ)
    (h : ∀ c : ℕ, 1 ≤ c → c ≤ m → zext a ((j c : ℤ) - i 0) = 0) :
    seqMinor a (m + 1) i j =
      zext a ((j 0 : ℤ) - i 0) * seqMinor a m (fun l => i (l + 1)) (fun l => j (l + 1)) := by
  unfold seqMinor
  rw [det_of_succ_row_single _ (fun c => by
    simp only [Fin.val_succ, Fin.val_zero]
    exact h _ (by omega) (by omega))]
  simp [Fin.val_succ]

theorem seqMinor_succ_succ_run (a : ℕ → ℝ) (m : ℕ) (i j : ℕ → ℕ)
    (h : ∀ c : ℕ, 2 ≤ c → c ≤ m + 1 → zext a ((j c : ℤ) - i 0) = 0)
    (hcol : ∀ r : ℕ, 2 ≤ r → r ≤ m + 1 → zext a ((j 0 : ℤ) - i r) = 0) :
    seqMinor a (m + 2) i j =
      zext a ((j 0 : ℤ) - i 0) * seqMinor a (m + 1) (fun l => i (l + 1)) (fun l => j (l + 1)) -
        zext a ((j 1 : ℤ) - i 0) * zext a ((j 0 : ℤ) - i 1) *
          seqMinor a m (fun l => i (l + 2)) (fun l => j (l + 2)) := by
  unfold seqMinor
  rw [det_of_succ_succ_row_two _
    (fun c => by
      simp only [Fin.val_succ, Fin.val_zero]
      exact h _ (by omega) (by omega))
    (fun r => by
      simp only [Fin.val_succ, Fin.val_zero]
      exact hcol _ (by omega) (by omega))]
  simp [Fin.val_succ]

/-- The joint invariant: nonnegativity, and the Chebyshev factorisation along a `d = 1` run. -/
theorem seqMinor_cosQuad_invariant {k : ℕ} {ψ : ℝ} (h0 : 0 ≤ ψ)
    (hk : ((k : ℝ) + 1) * ψ ≤ Real.pi) :
    ∀ m ≤ k, ∀ i j : ℕ → ℕ, StrictMono i → StrictMono j →
      0 ≤ seqMinor (cosQuad ψ) m i j ∧
      (1 ≤ m → j 0 = i 0 + 1 → ∃ r : ℕ, ∃ X : ℝ, 1 ≤ r ∧ r ≤ m ∧ 0 ≤ X ∧
        seqMinor (cosQuad ψ) m i j = chebU (Real.cos ψ) r * X ∧
        seqMinor (cosQuad ψ) (m - 1) (fun l => i (l + 1)) (fun l => j (l + 1)) =
          chebU (Real.cos ψ) (r - 1) * X) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro hmk i j hi hj
  set q := cosQuad ψ with hq
  -- part B: the run factorisation
  have partB : 1 ≤ m → j 0 = i 0 + 1 → ∃ r : ℕ, ∃ X : ℝ, 1 ≤ r ∧ r ≤ m ∧ 0 ≤ X ∧
      seqMinor q m i j = chebU (Real.cos ψ) r * X ∧
      seqMinor q (m - 1) (fun l => i (l + 1)) (fun l => j (l + 1)) =
        chebU (Real.cos ψ) (r - 1) * X := by
    intro hm1 hd
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    have hd' : ((j 0 : ℤ) - i 0) = 1 := by omega
    have htail := (ih n (by omega) (by omega) (fun l => i (l + 1)) (fun l => j (l + 1))
      (fun a b hab => hi (by omega)) (fun a b hab => hj (by omega)))
    -- the break cases
    by_cases hbreak : n = 0 ∨ i 0 + 1 < i 1 ∨ j 0 + 1 < j 1
    · refine ⟨1, seqMinor q n (fun l => i (l + 1)) (fun l => j (l + 1)), le_rfl, by omega,
        htail.1, ?_, by simp [chebU]⟩
      rcases hbreak with hn | hi1 | hj1
      · subst hn
        rw [seqMinor_succ_of_col _ _ _ _ (fun r hr1 hr2 => by omega), hd', hq,
          zext_cosQuad_one]
        simp [chebU]
      · rw [seqMinor_succ_of_col _ _ _ _ (fun r hr1 _ => by
          have : i 1 ≤ i r := hi.monotone hr1
          exact zext_cosQuad_of_neg ψ (by omega)), hd', hq, zext_cosQuad_one]
        simp [chebU]
      · rw [seqMinor_succ_of_row _ _ _ _ (fun c hc1 _ => by
          have : j 1 ≤ j c := hj.monotone hc1
          exact zext_cosQuad_of_gt ψ (by omega)), hd', hq, zext_cosQuad_one]
        simp [chebU]
    · push Not at hbreak
      obtain ⟨hn0, hi1, hj1⟩ := hbreak
      have hi1' : i 1 = i 0 + 1 := by have := hi (show 0 < 1 by norm_num); omega
      have hj1' : j 1 = j 0 + 1 := by have := hj (show 0 < 1 by norm_num); omega
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      -- the tail is again a `d = 1` minor
      obtain ⟨r', X, hr'1, hr'n, hX, hT1, hT2⟩ := htail.2 (by omega) (by simp; omega)
      refine ⟨r' + 1, X, by omega, by omega, hX, ?_, ?_⟩
      · rw [seqMinor_succ_succ_run _ _ _ _
          (fun c hc2 _ => by
            have : j 2 ≤ j c := hj.monotone hc2
            have : j 1 < j 2 := hj (by norm_num)
            exact zext_cosQuad_of_gt ψ (by omega))
          (fun r hr2 _ => by
            have : i 2 ≤ i r := hi.monotone hr2
            have : i 1 < i 2 := hi (by norm_num)
            exact zext_cosQuad_of_neg ψ (by omega))]
        rw [hd', show ((j 1 : ℤ) - i 0) = 2 by omega, show ((j 0 : ℤ) - i 1) = 0 by omega, hq,
          zext_cosQuad_one, zext_cosQuad_two, zext_cosQuad_zero, hT1]
        simp only [Nat.add_sub_cancel] at hT2
        rw [hT2]
        obtain ⟨s, rfl⟩ : ∃ s, r' = s + 1 := ⟨r' - 1, by omega⟩
        rw [show s + 1 + 1 = s + 2 by ring, chebU_succ_succ]
        simp only [Nat.add_sub_cancel]
        ring
      · simpa using hT1
  refine ⟨?_, partB⟩
  -- part A: nonnegativity
  rcases Nat.eq_zero_or_pos m with rfl | hmpos
  · rw [seqMinor_zero]; norm_num
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have htail := (ih n (by omega) (by omega) (fun l => i (l + 1)) (fun l => j (l + 1))
    (fun a b hab => hi (by omega)) (fun a b hab => hj (by omega))).1
  by_cases hd1 : j 0 = i 0 + 1
  · obtain ⟨r, X, hr1, hrm, hX, hT, -⟩ := partB (by omega) hd1
    rw [hT]
    refine mul_nonneg (chebU_cos_nonneg h0 ?_) hX
    have : (r : ℝ) ≤ k := by exact_mod_cast hrm.trans hmk
    nlinarith
  · rcases lt_trichotomy (j 0 : ℤ) (i 0) with hlt | heq | hgt
    · rw [seqMinor_succ_of_col _ _ _ _ (fun r hr1 _ => by
        have : i 0 ≤ i r := hi.monotone (Nat.zero_le r)
        exact zext_cosQuad_of_neg ψ (by omega)), zext_cosQuad_of_neg ψ (by omega), zero_mul]
    · rw [seqMinor_succ_of_col _ _ _ _ (fun r hr1 _ => by
        have : i 0 < i r := hi (by omega)
        exact zext_cosQuad_of_neg ψ (by omega)), show ((j 0 : ℤ) - i 0) = 0 by omega,
        zext_cosQuad_zero, one_mul]
      exact htail
    · by_cases hd2 : (j 0 : ℤ) - i 0 = 2
      · rw [seqMinor_succ_of_row _ _ _ _ (fun c hc1 _ => by
          have : j 0 < j c := hj (by omega)
          exact zext_cosQuad_of_gt ψ (by omega)), hd2, zext_cosQuad_two, one_mul]
        exact htail
      · rw [seqMinor_succ_of_row _ _ _ _ (fun c hc1 _ => by
          have : j 0 < j c := hj (by omega)
          exact zext_cosQuad_of_gt ψ (by omega)), zext_cosQuad_of_gt ψ (by omega), zero_mul]

/-- Strictly increasing extension of an increasing `Fin m`-indexed sequence. -/
def finExtend {m : ℕ} (i : Fin m → ℕ) (l : ℕ) : ℕ :=
  if h : l < m then i ⟨l, h⟩ else (∑ c, i c) + 1 + l

theorem finExtend_apply {m : ℕ} (i : Fin m → ℕ) (c : Fin m) : finExtend i c = i c := by
  simp [finExtend, c.2]

theorem strictMono_finExtend {m : ℕ} {i : Fin m → ℕ} (hi : StrictMono i) :
    StrictMono (finExtend i) := by
  intro l l' hll'
  have hbound : ∀ c : Fin m, i c < (∑ c, i c) + 1 := fun c =>
    Nat.lt_succ_of_le (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ c))
  unfold finExtend
  by_cases hl' : l' < m
  · have hl : l < m := hll'.trans hl'
    rw [dif_pos hl, dif_pos hl']
    exact hi (show (⟨l, hl⟩ : Fin m) < ⟨l', hl'⟩ from hll')
  · rw [dif_neg hl']
    by_cases hl : l < m
    · rw [dif_pos hl]
      have := hbound ⟨l, hl⟩
      omega
    · rw [dif_neg hl]
      omega

theorem toeplitzMinor_eq_seqMinor (a : ℕ → ℝ) {m : ℕ} (i j : Fin m → ℕ) :
    toeplitzMinor a m i j = seqMinor a m (finExtend i) (finExtend j) := by
  unfold toeplitzMinor seqMinor
  congr 1
  ext r c
  simp [finExtend_apply]

namespace PFSeq

/-- **The quadratic `1 + 2cos ψ z + z²` is `PF_k` for `(k + 1)ψ ≤ π`.** -/
theorem cosQuadratic {k : ℕ} {ψ : ℝ} (h0 : 0 ≤ ψ) (hk : ((k : ℝ) + 1) * ψ ≤ Real.pi) :
    PFSeq k (fun n => if n = 0 then 1 else if n = 1 then 2 * Real.cos ψ else if n = 2 then 1
      else 0) := by
  intro m hm i j hi hj
  have := (seqMinor_cosQuad_invariant h0 hk m hm (finExtend i) (finExtend j)
    (strictMono_finExtend hi) (strictMono_finExtend hj)).1
  rw [← toeplitzMinor_eq_seqMinor] at this
  exact this

/-- Multiplying a `PF_k` sequence by a geometric sequence `rⁿ`, `r > 0`, keeps it `PF_k`. -/
theorem geom_mul {k : ℕ} {a : ℕ → ℝ} (ha : PFSeq k a) {r : ℝ} (hr : 0 < r) :
    PFSeq k (fun n => r ^ n * a n) := by
  intro m hm i j hi hj
  have hz : ∀ z : ℤ, zext (fun n => r ^ n * a n) z = r ^ z * zext a z := by
    intro z
    unfold zext
    split_ifs with h
    · show r ^ z.toNat * a z.toNat = _
      rw [← zpow_natCast, Int.toNat_of_nonneg h]
    · rw [mul_zero]
  have hentry : ∀ (rr cc : Fin m), zext (fun n => r ^ n * a n) ((j cc : ℤ) - i rr) =
      r ^ (-(i rr : ℤ)) * (r ^ (j cc : ℤ) * zext a ((j cc : ℤ) - i rr)) := by
    intro rr cc
    rw [hz, zpow_sub₀ hr.ne', div_eq_mul_inv, ← _root_.zpow_neg]
    ring
  have hM : toeplitzMinor (fun n => r ^ n * a n) m i j =
      (∏ rr, r ^ (-(i rr : ℤ))) * ((∏ cc, r ^ (j cc : ℤ)) * toeplitzMinor a m i j) := by
    unfold toeplitzMinor
    simp_rw [hentry]
    set v : Fin m → ℝ := fun rr => r ^ (-(i rr : ℤ))
    set w : Fin m → ℝ := fun cc => r ^ (j cc : ℤ)
    set Z : Matrix (Fin m) (Fin m) ℝ := Matrix.of fun rr cc => zext a ((j cc : ℤ) - i rr)
    calc (Matrix.of fun rr cc => v rr * (w cc * Z rr cc)).det
        = (Matrix.of fun rr cc => v rr * (Matrix.of fun rr cc => w cc * Z rr cc) rr cc).det := rfl
      _ = (∏ rr, v rr) * (Matrix.of fun rr cc => w cc * Z rr cc).det :=
          Matrix.det_mul_column _ _
      _ = (∏ rr, v rr) * ((∏ cc, w cc) * Z.det) := by
          rw [Matrix.det_mul_row]
  rw [hM]
  have h1 : 0 ≤ ∏ rr, r ^ (-(i rr : ℤ)) := Finset.prod_nonneg fun _ _ => (zpow_pos hr _).le
  have h2 : 0 ≤ ∏ cc, r ^ (j cc : ℤ) := Finset.prod_nonneg fun _ _ => (zpow_pos hr _).le
  exact mul_nonneg h1 (mul_nonneg h2 (ha m hm i j hi hj))

/-- The scaled quadratic `rⁿ (1, 2cos ψ, 1)ₙ` is `PF_k` for `(k + 1)ψ ≤ π`, `r > 0`. -/
theorem cosQuadratic_geom {k : ℕ} {ψ r : ℝ} (h0 : 0 ≤ ψ) (hk : ((k : ℝ) + 1) * ψ ≤ Real.pi)
    (hr : 0 < r) :
    PFSeq k (fun n => r ^ n * (if n = 0 then 1 else if n = 1 then 2 * Real.cos ψ
      else if n = 2 then 1 else 0)) :=
  geom_mul (cosQuadratic h0 hk) hr

end PFSeq

end

end GaloisForLFunctions.HTGeometry
