import GaloisForLFunctions.HTGeometry.ConstraintRelativity.GibbsModularPhase

/-!
# Closing a polygon with unit phases

Let `w_0, …, w_{N-1} ∈ ℂ` have moduli at most `B` and total modulus `T ≥ 12B + 3|v|`.  Then there are unit
scalars `u_n` with `Σ u_n w_n = v`, and a second such family differing from the first at an index with
`w_n ≠ 0`.

Cutting the prefix sums at `T/3` and `2T/3` splits the indices into three consecutive groups of total
moduli `S₁, S₂, S₃`, each within `B` of `T/3`.  The lengths `S₁, S₂, S₃ + |v|` satisfy strict triangle
inequalities; a triangle `z₀ + z₁ + z₂ = 0` with these side lengths, rotated so that `z₂ = S₃d₃ - v`
(`d₃ = -v/|v|`), aligns each group along one direction.  Reflecting the triangle across the line of `z₂`
gives a second, different, solution.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The direction of a complex number, `1` at `0`. -/
def unitDir (z : ℂ) : ℂ := if z = 0 then 1 else z / (‖z‖ : ℂ)

theorem norm_unitDir (z : ℂ) : ‖unitDir z‖ = 1 := by
  unfold unitDir; split_ifs with h
  · simp
  · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (norm_pos_iff.mpr h), div_self
      (norm_pos_iff.mpr h).ne']

theorem unitDir_mul_norm (z : ℂ) : unitDir z * (‖z‖ : ℂ) = z := by
  unfold unitDir; split_ifs with h
  · simp [h]
  · field_simp [(Complex.ofReal_ne_zero.mpr (norm_pos_iff.mpr h).ne')]

/-- The phase aligning `w` with direction `d`: `u w = d |w|`. -/
def alignPhase (d w : ℂ) : ℂ := d * (starRingEnd ℂ) (unitDir w)

theorem norm_alignPhase {d : ℂ} (hd : ‖d‖ = 1) (w : ℂ) : ‖alignPhase d w‖ = 1 := by
  unfold alignPhase; rw [norm_mul, RCLike.norm_conj, norm_unitDir, hd, one_mul]

theorem alignPhase_mul (d w : ℂ) : alignPhase d w * w = d * (‖w‖ : ℂ) := by
  unfold alignPhase
  by_cases h : w = 0
  · simp [h]
  · have hw : unitDir w = w / (‖w‖ : ℂ) := by simp [unitDir, h]
    rw [hw]
    have hn : (‖w‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_pos_iff.mpr h).ne'
    rw [map_div₀, Complex.conj_ofReal]
    have : (starRingEnd ℂ) w * w = (‖w‖ : ℂ) ^ 2 := by rw [mul_comm, Complex.mul_conj']
    field_simp
    linear_combination d * this

/-- Reflection across the line through `0` and `e`, for `‖e‖ = 1`. -/
def reflectLine (e z : ℂ) : ℂ := e ^ 2 * (starRingEnd ℂ) z

theorem norm_reflectLine {e : ℂ} (he : ‖e‖ = 1) (z : ℂ) : ‖reflectLine e z‖ = ‖z‖ := by
  unfold reflectLine; rw [norm_mul, norm_pow, he, one_pow, one_mul, RCLike.norm_conj]

theorem reflectLine_add (e z w : ℂ) : reflectLine e (z + w) = reflectLine e z + reflectLine e w := by
  unfold reflectLine; rw [map_add]; ring

theorem reflectLine_self {e : ℂ} (he : ‖e‖ = 1) (r : ℝ) : reflectLine e (r * e) = r * e := by
  unfold reflectLine
  rw [map_mul, Complex.conj_ofReal]
  have : e * (starRingEnd ℂ) e = 1 := by rw [Complex.mul_conj', he]; simp
  linear_combination (r : ℂ) * e * this

/-- A nondegenerate triangle is moved by the reflection across one of its sides. -/
theorem reflectLine_ne_of_strict {z₀ z₁ z₂ : ℂ} (hsum : z₀ + z₁ + z₂ = 0) (hz₂ : z₂ ≠ 0)
    (hstrict : ‖z₁‖ < ‖z₀‖ + ‖z₂‖) (hstrict' : ‖z₀‖ < ‖z₁‖ + ‖z₂‖) (hstrict'' : ‖z₂‖ < ‖z₀‖ + ‖z₁‖) :
    reflectLine (unitDir z₂) z₀ ≠ z₀ := by
  intro heq
  set e := unitDir z₂ with he
  have he1 : ‖e‖ = 1 := norm_unitDir z₂
  -- `z₀ = e² conj z₀` forces `z₀ = r e` with `r` real
  have hr : ∃ r : ℝ, z₀ = r * e := by
    refine ⟨(z₀ * (starRingEnd ℂ) e).re, ?_⟩
    have hconj : (starRingEnd ℂ) (z₀ * (starRingEnd ℂ) e) = z₀ * (starRingEnd ℂ) e := by
      unfold reflectLine at heq
      have hee : e * (starRingEnd ℂ) e = 1 := by rw [Complex.mul_conj', he1]; simp
      rw [map_mul, Complex.conj_conj]
      calc (starRingEnd ℂ) z₀ * e = (starRingEnd ℂ) z₀ * e * (e * (starRingEnd ℂ) e) := by
            rw [hee, mul_one]
        _ = (e ^ 2 * (starRingEnd ℂ) z₀) * (starRingEnd ℂ) e := by ring
        _ = z₀ * (starRingEnd ℂ) e := by rw [heq]
    have hreal := Complex.conj_eq_iff_re.mp hconj
    have hee : (starRingEnd ℂ) e * e = 1 := by rw [mul_comm, Complex.mul_conj', he1]; simp
    calc z₀ = z₀ * ((starRingEnd ℂ) e * e) := by rw [hee, mul_one]
      _ = (z₀ * (starRingEnd ℂ) e) * e := by ring
      _ = ((z₀ * (starRingEnd ℂ) e).re : ℂ) * e := by rw [hreal]
  obtain ⟨r, hr⟩ := hr
  set n : ℝ := ‖z₂‖ with hn
  have hnpos : 0 < n := norm_pos_iff.mpr hz₂
  have hz2 : z₂ = (n : ℂ) * e := by rw [he, mul_comm, hn, unitDir_mul_norm]
  have hz1 : z₁ = -((r + n : ℝ) : ℂ) * e := by
    have : z₁ = -(z₀ + z₂) := by linear_combination hsum
    rw [this, hr, hz2]; push_cast; ring
  have n0 : ‖z₀‖ = |r| := by rw [hr, norm_mul, he1, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have n1 : ‖z₁‖ = |r + n| := by
    rw [hz1, norm_mul, he1, mul_one, norm_neg, Complex.norm_real, Real.norm_eq_abs]
  rw [n0, n1] at hstrict hstrict' hstrict''
  rcases le_total 0 r with hr0 | hr0
  · rw [abs_of_nonneg hr0, abs_of_nonneg (by linarith : 0 ≤ r + n)] at hstrict; linarith
  · rcases le_total 0 (r + n) with h' | h'
    · rw [abs_of_nonpos hr0, abs_of_nonneg h'] at hstrict''; linarith
    · rw [abs_of_nonpos hr0, abs_of_nonpos h'] at hstrict'; linarith

theorem alignPhase_injective {d d' w : ℂ} (h : alignPhase d w = alignPhase d' w) : d = d' := by
  unfold alignPhase at h
  have hne : (starRingEnd ℂ) (unitDir w) ≠ 0 := by
    intro h0
    have := norm_unitDir w
    rw [← RCLike.norm_conj, h0, norm_zero] at this
    exact zero_ne_one this
  exact mul_right_cancel₀ hne h

/-- Prefix sums of moduli. -/
def prefixMass (w : ℕ → ℂ) (k : ℕ) : ℝ := ∑ n ∈ Finset.range k, ‖w n‖

theorem prefixMass_mono (w : ℕ → ℂ) {j k : ℕ} (h : j ≤ k) : prefixMass w j ≤ prefixMass w k := by
  unfold prefixMass
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr h)
    (fun _ _ _ => norm_nonneg _)

theorem prefixMass_succ (w : ℕ → ℂ) (k : ℕ) : prefixMass w (k + 1) = prefixMass w k + ‖w k‖ := by
  unfold prefixMass; rw [Finset.sum_range_succ]

/-- The first index at which the prefix mass reaches `x`. -/
theorem exists_cut (w : ℕ → ℂ) (N : ℕ) {B x : ℝ} (hw : ∀ n < N, ‖w n‖ ≤ B) (hx0 : 0 < x)
    (hxN : x ≤ prefixMass w N) :
    ∃ k ≤ N, x ≤ prefixMass w k ∧ prefixMass w k < x + B ∧ 0 < k := by
  classical
  have hex : ∃ k, x ≤ prefixMass w k := ⟨N, hxN⟩
  set k := Nat.find hex with hk
  have hkx : x ≤ prefixMass w k := Nat.find_spec hex
  have hkN : k ≤ N := Nat.find_min' hex hxN
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h] at hkx; simp [prefixMass] at hkx; linarith
    · exact h
  have hprev : prefixMass w (k - 1) < x := by
    have := Nat.find_min hex (show k - 1 < k by omega)
    exact lt_of_not_ge this
  refine ⟨k, hkN, hkx, ?_, hk0⟩
  have hsucc := prefixMass_succ w (k - 1)
  rw [show k - 1 + 1 = k by omega] at hsucc
  have hb := hw (k - 1) (by omega)
  linarith

/-- **Two unit polygons.** -/
theorem exists_two_unit_polygons (w : ℕ → ℂ) (N : ℕ) (v : ℂ) {B : ℝ} (hB : 0 < B)
    (hw : ∀ n < N, ‖w n‖ ≤ B) (hT : 12 * B + 3 * ‖v‖ ≤ prefixMass w N) :
    ∃ u u' : ℕ → ℂ, (∀ n, ‖u n‖ = 1) ∧ (∀ n, ‖u' n‖ = 1) ∧
      ∑ n ∈ Finset.range N, u n * w n = v ∧ ∑ n ∈ Finset.range N, u' n * w n = v ∧
        ∃ n < N, w n ≠ 0 ∧ u n ≠ u' n := by
  classical
  set T := prefixMass w N with hTdef
  have hv0 := norm_nonneg v
  have hT0 : 0 < T := by linarith
  obtain ⟨k₁, hk₁N, hk₁lo, hk₁hi, hk₁0⟩ := exists_cut w N hw (x := T / 3) (by positivity) (by linarith)
  obtain ⟨k₂, hk₂N, hk₂lo, hk₂hi, -⟩ := exists_cut w N hw (x := 2 * T / 3) (by positivity) (by linarith)
  have hk₁₂ : k₁ ≤ k₂ := by
    by_contra h
    push Not at h
    have := prefixMass_mono w (le_of_lt h)
    have hmono := prefixMass_mono w (show k₂ ≤ k₁ - 1 by omega)
    -- `P(k₁ - 1) < T/3` by minimality is not available here; use the cut bounds instead
    linarith [prefixMass_mono w (show k₂ ≤ k₁ by omega)]
  set S₁ := prefixMass w k₁
  set S₂ := prefixMass w k₂ - prefixMass w k₁
  set S₃ := T - prefixMass w k₂
  have hS₁lo : T / 3 ≤ S₁ := hk₁lo
  have hS₁hi : S₁ < T / 3 + B := hk₁hi
  have hS₂lo : T / 3 - B < S₂ := by simp only [S₂]; linarith
  have hS₂hi : S₂ < T / 3 + B := by simp only [S₂]; linarith
  have hS₃lo : T / 3 - B < S₃ := by simp only [S₃]; linarith
  have hS₃hi : S₃ ≤ T / 3 := by simp only [S₃]; linarith
  have hT3 : 4 * B + ‖v‖ ≤ T / 3 := by linarith
  set a := S₁; set b := S₂; set c := S₃ + ‖v‖
  have ha : 0 < a := by linarith
  have hb : 0 < b := by linarith
  have hc : 0 < c := by simp only [c]; linarith
  have t1 : c < a + b := by simp only [c]; linarith
  have t2 : a < b + c := by simp only [c]; linarith
  have t3 : b < a + c := by simp only [c]; linarith
  obtain ⟨z, hz, hzsum⟩ := _root_.HTGeometry.ConstraintRelativity.exists_sum_eq_zero_of_triangle (r := ![a, b, c])
    (by intro i; fin_cases i <;> simp [ha, hb, hc]) (by simp; linarith) (by simp; linarith)
    (by simp; linarith)
  have hz0 : ‖z 0‖ = a := by simpa using hz 0
  have hz1 : ‖z 1‖ = b := by simpa using hz 1
  have hz2 : ‖z 2‖ = c := by simpa using hz 2
  have hz2ne : z 2 ≠ 0 := norm_pos_iff.mp (by rw [hz2]; exact hc)
  set vh : ℂ := unitDir v with hvh
  have hvhn : ‖vh‖ = 1 := norm_unitDir v
  have hv : v = vh * (‖v‖ : ℂ) := by rw [hvh]; exact (unitDir_mul_norm v).symm
  set d₃ : ℂ := -vh with hd₃
  have hd₃n : ‖d₃‖ = 1 := by rw [hd₃, norm_neg, hvhn]
  set q : ℂ := (S₃ : ℂ) * d₃ - v with hq
  have hqn : ‖q‖ = c := by
    have : q = -(((S₃ + ‖v‖ : ℝ) : ℂ) * vh) := by
      rw [hq, hd₃]; push_cast
      linear_combination -hv
    rw [this, norm_neg, norm_mul, hvhn, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
  set ζ : ℂ := q / z 2 with hζ
  have hζn : ‖ζ‖ = 1 := by rw [hζ, norm_div, hqn, hz2, div_self hc.ne']
  have hζz2 : ζ * z 2 = q := by rw [hζ]; field_simp
  -- the directions of the three groups, for a triangle `y`
  have build : ∀ y : Fin 3 → ℂ, ‖y 0‖ = a → ‖y 1‖ = b → y 0 + y 1 + z 2 = 0 →
      ∃ u : ℕ → ℂ, (∀ n, ‖u n‖ = 1) ∧ ∑ n ∈ Finset.range N, u n * w n = v ∧
        ∀ n < k₁, u n = alignPhase (ζ * y 0 / (S₁ : ℂ)) (w n) := by
    intro y hy0 hy1 hysum
    set d₁ : ℂ := ζ * y 0 / (S₁ : ℂ)
    set d₂ : ℂ := ζ * y 1 / (S₂ : ℂ)
    have hd₁ : ‖d₁‖ = 1 := by
      simp only [d₁]; rw [norm_div, norm_mul, hζn, one_mul, hy0, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos ha, div_self ha.ne']
    have hd₂ : ‖d₂‖ = 1 := by
      simp only [d₂]; rw [norm_div, norm_mul, hζn, one_mul, hy1, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hb, div_self hb.ne']
    set dir : ℕ → ℂ := fun n => if n < k₁ then d₁ else if n < k₂ then d₂ else d₃
    have hdir : ∀ n, ‖dir n‖ = 1 := by
      intro n; simp only [dir]; split_ifs <;> assumption
    refine ⟨fun n => alignPhase (dir n) (w n), fun n => norm_alignPhase (hdir n) _, ?_, ?_⟩
    · simp_rw [alignPhase_mul]
      have hsplit : Finset.range N = Finset.range k₁ ∪ (Finset.Ico k₁ k₂ ∪ Finset.Ico k₂ N) := by
        ext n; simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]; omega
      have hd1 : Disjoint (Finset.range k₁) (Finset.Ico k₁ k₂ ∪ Finset.Ico k₂ N) := by
        rw [Finset.disjoint_left]; intro n h1 h2
        simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico] at h1 h2; omega
      have hd2 : Disjoint (Finset.Ico k₁ k₂) (Finset.Ico k₂ N) := by
        rw [Finset.disjoint_left]; intro n h1 h2
        simp only [Finset.mem_Ico] at h1 h2; omega
      rw [hsplit, Finset.sum_union hd1, Finset.sum_union hd2]
      have e1 : ∑ n ∈ Finset.range k₁, dir n * (‖w n‖ : ℂ) = d₁ * (S₁ : ℂ) := by
        have hS₁c : (S₁ : ℂ) = ∑ n ∈ Finset.range k₁, (‖w n‖ : ℂ) := by
          simp only [S₁, prefixMass]; push_cast; rfl
        rw [hS₁c, Finset.mul_sum]
        refine Finset.sum_congr rfl fun n hn => ?_
        rw [Finset.mem_range] at hn; simp [dir, hn]
      have e2 : ∑ n ∈ Finset.Ico k₁ k₂, dir n * (‖w n‖ : ℂ) = d₂ * (S₂ : ℂ) := by
        have hS₂ : S₂ = ∑ n ∈ Finset.Ico k₁ k₂, ‖w n‖ := by
          have h := Finset.sum_range_add_sum_Ico (fun n => ‖w n‖) hk₁₂
          simp only [S₂, prefixMass]; linarith
        rw [hS₂]; push_cast; rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n hn => ?_
        rw [Finset.mem_Ico] at hn
        simp [dir, show ¬ n < k₁ by omega, hn.2]
      have e3 : ∑ n ∈ Finset.Ico k₂ N, dir n * (‖w n‖ : ℂ) = d₃ * (S₃ : ℂ) := by
        have hS₃ : S₃ = ∑ n ∈ Finset.Ico k₂ N, ‖w n‖ := by
          have h := Finset.sum_range_add_sum_Ico (fun n => ‖w n‖) hk₂N
          simp only [S₃, hTdef, prefixMass]; linarith
        rw [hS₃]; push_cast; rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n hn => ?_
        rw [Finset.mem_Ico] at hn
        simp [dir, show ¬ n < k₁ by omega, show ¬ n < k₂ by omega]
      rw [e1, e2, e3]
      have hS₁ne : (S₁ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
      have hS₂ne : (S₂ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb.ne'
      simp only [d₁, d₂]
      field_simp
      have : ζ * (y 0 + y 1) = -q := by
        rw [← hζz2]; linear_combination ζ * hysum
      linear_combination this + (0 : ℂ) * hq
    · intro n hn; simp [dir, hn]
  -- first and reflected triangles
  set e := unitDir (z 2) with he
  have he1 : ‖e‖ = 1 := norm_unitDir _
  have hz2e : z 2 = ((‖z 2‖ : ℝ) : ℂ) * e := by rw [he, mul_comm, unitDir_mul_norm]
  have hrefl2 : reflectLine e (z 2) = z 2 := by
    conv_lhs => rw [hz2e]
    rw [reflectLine_self he1, ← hz2e]
  obtain ⟨u, hu, husum, hu0⟩ := build (fun i => z i) hz0 hz1 hzsum
  have hy0' : ‖reflectLine e (z 0)‖ = a := by rw [norm_reflectLine he1, hz0]
  have hy1' : ‖reflectLine e (z 1)‖ = b := by rw [norm_reflectLine he1, hz1]
  have hysum' : reflectLine e (z 0) + reflectLine e (z 1) + z 2 = 0 := by
    rw [← reflectLine_add, show z 0 + z 1 = -z 2 by linear_combination hzsum]
    unfold reflectLine; rw [map_neg, mul_neg]
    have : e ^ 2 * (starRingEnd ℂ) (z 2) = z 2 := hrefl2
    rw [this]; ring
  obtain ⟨u', hu', hu'sum, hu'0⟩ := build ![reflectLine e (z 0), reflectLine e (z 1), 0]
    (by simpa using hy0') (by simpa using hy1') (by simpa using hysum')
  refine ⟨u, u', hu, hu', husum, hu'sum, ?_⟩
  -- an index in the first group with `w n ≠ 0`
  have hpos : 0 < ∑ n ∈ Finset.range k₁, ‖w n‖ := ha
  obtain ⟨n, hn, hwn⟩ : ∃ n ∈ Finset.range k₁, w n ≠ 0 := by
    by_contra h
    push Not at h
    have : ∑ n ∈ Finset.range k₁, ‖w n‖ = 0 := Finset.sum_eq_zero fun n hn => by rw [h n hn, norm_zero]
    linarith
  rw [Finset.mem_range] at hn
  refine ⟨n, by omega, hwn, fun heq => ?_⟩
  rw [hu0 n hn, hu'0 n hn] at heq
  have hd := alignPhase_injective heq
  have hS₁ne : (S₁ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hζne : ζ ≠ 0 := by intro h0; rw [h0, norm_zero] at hζn; exact zero_ne_one hζn
  have hzeq : z 0 = reflectLine e (z 0) := by
    have h' := hd
    simp only [Matrix.cons_val_zero] at h'
    rw [div_left_inj' hS₁ne] at h'
    exact mul_left_cancel₀ hζne h'
  exact reflectLine_ne_of_strict hzsum hz2ne (by rw [hz0, hz1, hz2]; exact t3)
    (by rw [hz0, hz1, hz2]; exact t2) (by rw [hz0, hz1, hz2]; exact t1) hzeq.symm

end

end GaloisForLFunctions.HTGeometry
