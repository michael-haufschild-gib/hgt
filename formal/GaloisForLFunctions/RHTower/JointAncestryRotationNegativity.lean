import GaloisForLFunctions.RHTower.JointAncestryPhaseOrbitMoments

/-!
# A dominant exponential on a large circle is negative on a fixed fraction of samples

Let `E(ξ) = Σ_s b_s e^{g_s ξ}` be a finite exponential sum with unit frequencies `g_s`.  Fix a
frequency `g₀`, let `B₀ = Σ_{g_s = g₀} b_s` with `|B₀| ≥ β > 0`, and suppose every other frequency
satisfies `Re(g_s ḡ₀) ≤ 1 − κ`.  Sample the circle `|ξ| = R` at the `N`-th roots of unity,
`ξ_j = ω^j ζ`.

**Theorem** (`card_rotation_negative`).  There are `R₀` and `c > 0`, depending only on
`β, κ, M = Σ|b_s|` and a bound `W₀` for a real shift `L`, such that for every `R₁` and every
`N ≥ 6R₁ + 2`, every `ζ` with `R₀ ≤ |ζ| ≤ R₁`, and every perturbation `|e_j| ≤ 1`,
`L + Re E(ω^j ζ) + e_j < 0` for at least `cN` indices `j`.

Proof.  In the arc where `g₀ξ = Re^{iτ}`, `0 ≤ τ ≤ α = min(κ/4, 1)`, the dominant class is
`B₀ e^{R cos τ} e^{iR sin τ}` and the rest is smaller by `(M/β)e^{−5κR/8}`.  The phase
`R sin τ + arg B₀` runs monotonically through `≥ R sin α/(2π) − 3/2` full periods.  In each period
the arc where its cosine is `≤ −½` pulls back to a `τ`-interval of length `≥ 2π/(3R)`, which
contains `≥ N/(6R)` sample angles.  On these samples `L + Re E + e_j ≤ W₀ + 1 − ¼βe^{R/2} < 0`.
-/

open Complex Finset
open scoped ComplexConjugate

namespace RHTower

noncomputable section

/-! ## Elementary bounds -/

theorem cos_le_neg_half_of_mem_add_int {x : ℝ} {m : ℤ} (h1 : 2 * Real.pi / 3 + 2 * Real.pi * m ≤ x)
    (h2 : x ≤ 4 * Real.pi / 3 + 2 * Real.pi * m) : Real.cos x ≤ -1 / 2 := by
  have hred : Real.cos x = -Real.cos (x - 2 * Real.pi * m - Real.pi) := by
    rw [show x - 2 * Real.pi * m - Real.pi = (x - Real.pi) - (m : ℝ) * (2 * Real.pi) by ring,
      Real.cos_sub_int_mul_two_pi, Real.cos_sub_pi, neg_neg]
  rw [hred]
  set y := x - 2 * Real.pi * m - Real.pi
  have hy : |y| ≤ Real.pi / 3 := by
    rw [abs_le]; constructor <;> linarith
  have hcy : Real.cos (Real.pi / 3) ≤ Real.cos |y| :=
    Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg y) (by linarith [Real.pi_pos]) hy
  rw [Real.cos_abs, Real.cos_pi_div_three] at hcy
  linarith

/-- At least `⌊y⌋` naturals `t < n` lie in `[x, x + y]`. -/
theorem card_range_filter_mem_Icc_ge {n : ℕ} {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : x + y < n) :
    ⌊y⌋₊ ≤ ((range n).filter fun t : ℕ => x ≤ t ∧ (t : ℝ) ≤ x + y).card := by
  have h := Finset.card_le_card_of_injOn (s := range ⌊y⌋₊)
    (t := (range n).filter fun t : ℕ => x ≤ t ∧ (t : ℝ) ≤ x + y) (fun i => ⌈x⌉₊ + i)
    (by
      intro i hi
      have hi' : i < ⌊y⌋₊ := Finset.mem_range.mp hi
      have hc := Nat.ceil_lt_add_one hx
      have hfy : ((i : ℕ) : ℝ) + 1 ≤ y := by
        have : (i : ℝ) + 1 ≤ ⌊y⌋₊ := by exact_mod_cast hi'
        linarith [Nat.floor_le hy]
      have hup : ((⌈x⌉₊ + i : ℕ) : ℝ) ≤ x + y := by push_cast; linarith
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq]
      refine ⟨?_, ?_, hup⟩
      · have : ((⌈x⌉₊ + i : ℕ) : ℝ) < n := lt_of_le_of_lt hup hxy
        exact_mod_cast this
      · push_cast; linarith [Nat.le_ceil x, (Nat.cast_nonneg i : (0 : ℝ) ≤ i)])
    (fun i _ j _ h => by simpa using h)
  simpa using h

/-! ## Counting good samples on the arc -/

/-- **Good samples.**  For samples `φ_t = φ₀ + 2πt/N`, `0 ≤ φ₀ < 2π/N`, at least
`(sin α/(24π))N` indices `t < N` have `φ_t ≤ α` and `cos(R sin φ_t + c) ≤ −½`. -/
theorem card_good_samples {R α c φ₀ : ℝ} {N : ℕ} (hR : 0 < R) (hα : 0 < α)
    (hαπ : α ≤ Real.pi / 2) (hφ₀ : 0 ≤ φ₀) (hφN : φ₀ < 2 * Real.pi / N) (hN : 6 * R ≤ N)
    (hRα : 16 * Real.pi ≤ R * Real.sin α) :
    Real.sin α / (24 * Real.pi) * N ≤
      ((range N).filter fun t : ℕ => φ₀ + 2 * Real.pi * t / N ≤ α ∧
        Real.cos (R * Real.sin (φ₀ + 2 * Real.pi * t / N) + c) ≤ -1 / 2).card := by
  have hπ := Real.pi_pos
  have hNpos : (0 : ℝ) < N := by linarith
  have hsinα : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα (by linarith)
  have hsinα1 : Real.sin α ≤ 1 := Real.sin_le_one α
  set mlo : ℤ := ⌈(2 * Real.pi * R / N + c - 2 * Real.pi / 3) / (2 * Real.pi)⌉ with hmlo
  set mhi : ℤ := ⌊(R * Real.sin α - 4 * Real.pi / 3 + c) / (2 * Real.pi)⌋ with hmhi
  set lo : ℤ → ℝ := fun m => (2 * Real.pi / 3 - c + 2 * Real.pi * m) / R with hlo
  set hi : ℤ → ℝ := fun m => (4 * Real.pi / 3 - c + 2 * Real.pi * m) / R with hhi
  set T : ℤ → Finset ℕ := fun m => (range N).filter fun t : ℕ =>
    Real.arcsin (lo m) ≤ φ₀ + 2 * Real.pi * t / N ∧ φ₀ + 2 * Real.pi * t / N ≤ Real.arcsin (hi m)
    with hT
  -- bounds on `lo` and `hi` for `m` in range
  have hlo_ge : ∀ m ∈ Finset.Icc mlo mhi, 2 * Real.pi / N ≤ lo m := by
    intro m hm
    have h1 : mlo ≤ m := (Finset.mem_Icc.mp hm).1
    have h2 : (2 * Real.pi * R / N + c - 2 * Real.pi / 3) / (2 * Real.pi) ≤ m :=
      (Int.ceil_le.mp h1)
    rw [div_le_iff₀ (by positivity)] at h2
    simp only [hlo]
    rw [le_div_iff₀ hR]
    have : 2 * Real.pi / N * R = 2 * Real.pi * R / N := by ring
    linarith
  have hhi_le : ∀ m ∈ Finset.Icc mlo mhi, hi m ≤ Real.sin α := by
    intro m hm
    have h1 : m ≤ mhi := (Finset.mem_Icc.mp hm).2
    have h2 : (m : ℝ) ≤ (R * Real.sin α - 4 * Real.pi / 3 + c) / (2 * Real.pi) :=
      Int.le_floor.mp h1
    rw [le_div_iff₀ (by positivity)] at h2
    simp only [hhi]
    rw [div_le_iff₀ hR]
    linarith
  have hlohi : ∀ m, hi m - lo m = 2 * Real.pi / 3 / R := by
    intro m; simp only [hhi, hlo]; field_simp; ring
  have hq : 0 < 2 * Real.pi / 3 / R := by positivity
  have hlo0 : ∀ m ∈ Finset.Icc mlo mhi, 0 ≤ lo m := fun m hm =>
    le_trans (by positivity) (hlo_ge m hm)
  have hhi1 : ∀ m ∈ Finset.Icc mlo mhi, hi m ≤ 1 := fun m hm => (hhi_le m hm).trans hsinα1
  have hlo1 : ∀ m ∈ Finset.Icc mlo mhi, lo m ≤ 1 := fun m hm => by
    have := hlohi m; have := hhi1 m hm; have : 0 < 2 * Real.pi / 3 / R := by positivity
    linarith
  -- arcsin facts
  have hJlo : ∀ m ∈ Finset.Icc mlo mhi, lo m ≤ Real.arcsin (lo m) := by
    intro m hm
    have h0 := hlo0 m hm
    have h1 := hlo1 m hm
    have hs := Real.sin_arcsin (by linarith : (-1 : ℝ) ≤ lo m) h1
    have := Real.sin_le (Real.arcsin_nonneg.mpr h0)
    linarith
  have hJhi : ∀ m ∈ Finset.Icc mlo mhi, Real.arcsin (hi m) ≤ α := by
    intro m hm
    calc Real.arcsin (hi m) ≤ Real.arcsin (Real.sin α) := Real.arcsin_le_arcsin (hhi_le m hm)
      _ = α := Real.arcsin_sin (by linarith) hαπ
  have hJlen : ∀ m ∈ Finset.Icc mlo mhi,
      2 * Real.pi / 3 / R ≤ Real.arcsin (hi m) - Real.arcsin (lo m) := by
    intro m hm
    have h0 := hlo0 m hm
    have hs1 := Real.sin_arcsin (by linarith : (-1 : ℝ) ≤ lo m) (hlo1 m hm)
    have hs2 := Real.sin_arcsin (by linarith [hlohi m, hq] : (-1 : ℝ) ≤ hi m) (hhi1 m hm)
    have hmono : Real.arcsin (lo m) ≤ Real.arcsin (hi m) :=
      Real.arcsin_le_arcsin (by linarith [hlohi m, hq])
    have := Real.abs_sin_sub_sin_le (Real.arcsin (hi m)) (Real.arcsin (lo m))
    rw [hs1, hs2, abs_of_nonneg (by linarith [hlohi m, hq]), abs_of_nonneg (by linarith)] at this
    linarith [hlohi m]
  -- each block has many samples
  have hblock : ∀ m ∈ Finset.Icc mlo mhi, ⌊(N : ℝ) / (3 * R)⌋₊ ≤ (T m).card := by
    intro m hm
    set x := (Real.arcsin (lo m) - φ₀) * N / (2 * Real.pi)
    set y := (Real.arcsin (hi m) - Real.arcsin (lo m)) * N / (2 * Real.pi)
    have hx : 0 ≤ x := by
      have : φ₀ ≤ Real.arcsin (lo m) := by linarith [hJlo m hm, hlo_ge m hm]
      positivity
    have hy0 : N / (3 * R) ≤ y := by
      have := hJlen m hm
      simp only [y]
      rw [le_div_iff₀ (by positivity)]
      have h3 : N / (3 * R) * (2 * Real.pi) = 2 * Real.pi / 3 / R * N := by field_simp
      rw [h3]; exact mul_le_mul_of_nonneg_right this hNpos.le
    have hy : 0 ≤ y := le_trans (by positivity) hy0
    have hxy : x + y < N := by
      have hJ := hJhi m hm
      have : x + y = (Real.arcsin (hi m) - φ₀) * N / (2 * Real.pi) := by simp only [x, y]; ring
      rw [this, div_lt_iff₀ (by positivity)]
      nlinarith
    have hA := card_range_filter_mem_Icc_ge (n := N) hx hy hxy
    have hsub : ((range N).filter fun t : ℕ => x ≤ t ∧ (t : ℝ) ≤ x + y) ⊆ T m := by
      intro t ht
      simp only [hT, Finset.mem_filter, Finset.mem_range] at ht ⊢
      refine ⟨ht.1, ?_, ?_⟩
      · have := ht.2.1
        simp only [x] at this
        rw [div_le_iff₀ (by positivity)] at this
        rw [show φ₀ + 2 * Real.pi * t / N = φ₀ + (2 * Real.pi * t) / N by ring,
          ← sub_le_iff_le_add', le_div_iff₀ hNpos]
        linarith
      · have := ht.2.2
        have hxy' : x + y = (Real.arcsin (hi m) - φ₀) * N / (2 * Real.pi) := by
          simp only [x, y]; ring
        rw [hxy', le_div_iff₀ (by positivity)] at this
        rw [show φ₀ + 2 * Real.pi * t / N = φ₀ + (2 * Real.pi * t) / N by ring,
          ← le_sub_iff_add_le', div_le_iff₀ hNpos]
        linarith
    exact (Nat.floor_le_floor hy0).trans (hA.trans (Finset.card_le_card hsub))
  -- blocks are good and disjoint
  have hgood : (Finset.Icc mlo mhi).biUnion T ⊆ (range N).filter fun t : ℕ =>
      φ₀ + 2 * Real.pi * t / N ≤ α ∧
        Real.cos (R * Real.sin (φ₀ + 2 * Real.pi * t / N) + c) ≤ -1 / 2 := by
    intro t ht
    obtain ⟨m, hm, htm⟩ := Finset.mem_biUnion.mp ht
    simp only [hT, Finset.mem_filter] at htm
    refine Finset.mem_filter.mpr ⟨htm.1, (htm.2.2).trans (hJhi m hm), ?_⟩
    set φ := φ₀ + 2 * Real.pi * t / N
    have hφ0 : 0 ≤ φ := le_trans (Real.arcsin_nonneg.mpr (hlo0 m hm)) htm.2.1
    have hφα : φ ≤ Real.pi / 2 := (htm.2.2.trans (hJhi m hm)).trans hαπ
    have hs1 := Real.sin_arcsin (by linarith [hlo0 m hm] : (-1 : ℝ) ≤ lo m) (hlo1 m hm)
    have hs2 := Real.sin_arcsin (by linarith [hlohi m, hlo0 m hm, hq] : (-1 : ℝ) ≤ hi m)
      (hhi1 m hm)
    have harc0 := Real.arcsin_nonneg.mpr (hlo0 m hm)
    have hsl : lo m ≤ Real.sin φ := by
      rw [← hs1]
      exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) hφα htm.2.1
    have hsh : Real.sin φ ≤ hi m := by
      rw [← hs2]
      exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (Real.arcsin_le_pi_div_two _)
        htm.2.2
    apply cos_le_neg_half_of_mem_add_int (m := m)
    · simp only [hlo] at hsl; rw [div_le_iff₀ hR] at hsl; nlinarith
    · simp only [hhi] at hsh; rw [le_div_iff₀ hR] at hsh; nlinarith
  have hdisj : (↑(Finset.Icc mlo mhi) : Set ℤ).PairwiseDisjoint T := by
    intro m hm m' hm' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro t htm htm'
    simp only [hT, Finset.mem_filter] at htm htm'
    rcases lt_or_gt_of_ne hne with h | h
    · have hlt : hi m < lo m' := by
        simp only [hhi, hlo]
        rw [div_lt_div_iff_of_pos_right hR]
        have : (m : ℝ) + 1 ≤ m' := by exact_mod_cast h
        nlinarith
      have := Real.arcsin_lt_arcsin (by linarith [hlo0 m hm, hlohi m, hq]) hlt (hlo1 m' hm')
      linarith [htm.2.2, htm'.2.1]
    · have hlt : hi m' < lo m := by
        simp only [hhi, hlo]
        rw [div_lt_div_iff_of_pos_right hR]
        have : (m' : ℝ) + 1 ≤ m := by exact_mod_cast h
        nlinarith
      have := Real.arcsin_lt_arcsin (by linarith [hlo0 m' hm', hlohi m', hq]) hlt (hlo1 m hm)
      linarith [htm.2.1, htm'.2.2]
  have hcard := Finset.card_biUnion hdisj
  have hsum : (Finset.Icc mlo mhi).card * ⌊(N : ℝ) / (3 * R)⌋₊ ≤
      ((Finset.Icc mlo mhi).biUnion T).card := by
    rw [hcard, ← smul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum hblock
  -- arithmetic
  have hIcc : R * Real.sin α / (2 * Real.pi) - 3 / 2 ≤ ((Finset.Icc mlo mhi).card : ℝ) := by
    rw [Int.card_Icc]
    have h1 : (R * Real.sin α - 4 * Real.pi / 3 + c) / (2 * Real.pi) - 1 < mhi := by
      have := Int.lt_floor_add_one ((R * Real.sin α - 4 * Real.pi / 3 + c) / (2 * Real.pi))
      linarith
    have h2 : (mlo : ℝ) < (2 * Real.pi * R / N + c - 2 * Real.pi / 3) / (2 * Real.pi) + 1 :=
      Int.ceil_lt_add_one _
    have hRN : R / N ≤ 1 / 6 := by rw [div_le_iff₀ hNpos]; linarith
    have hkey : R * Real.sin α / (2 * Real.pi) - 3 / 2 ≤ (mhi + 1 - mlo : ℤ) := by
      push_cast
      have e1 : (R * Real.sin α - 4 * Real.pi / 3 + c) / (2 * Real.pi) =
          R * Real.sin α / (2 * Real.pi) - 2 / 3 + c / (2 * Real.pi) := by field_simp; ring
      have e2 : (2 * Real.pi * R / N + c - 2 * Real.pi / 3) / (2 * Real.pi) =
          R / N + c / (2 * Real.pi) - 1 / 3 := by field_simp
      rw [e1] at h1; rw [e2] at h2
      linarith
    calc R * Real.sin α / (2 * Real.pi) - 3 / 2 ≤ ((mhi + 1 - mlo : ℤ) : ℝ) := hkey
      _ ≤ (((mhi + 1 - mlo).toNat : ℤ) : ℝ) := by exact_mod_cast Int.self_le_toNat _
      _ = (((mhi + 1 - mlo).toNat : ℕ) : ℝ) := by norm_cast
  have hfloor : (N : ℝ) / (6 * R) ≤ ⌊(N : ℝ) / (3 * R)⌋₊ := by
    have := Nat.lt_floor_add_one ((N : ℝ) / (3 * R))
    have h6 : 1 ≤ (N : ℝ) / (6 * R) := by rw [le_div_iff₀ (by positivity)]; linarith
    have : (N : ℝ) / (3 * R) = 2 * ((N : ℝ) / (6 * R)) := by field_simp; ring
    linarith
  have hfin : Real.sin α / (24 * Real.pi) * N ≤
      ((Finset.Icc mlo mhi).card : ℝ) * ⌊(N : ℝ) / (3 * R)⌋₊ := by
    have hA : R * Real.sin α / (4 * Real.pi) ≤ R * Real.sin α / (2 * Real.pi) - 3 / 2 := by
      have : R * Real.sin α / (4 * Real.pi) ≥ 4 := by
        rw [ge_iff_le, le_div_iff₀ (by positivity)]; linarith
      have e : R * Real.sin α / (2 * Real.pi) = 2 * (R * Real.sin α / (4 * Real.pi)) := by
        field_simp; ring
      linarith
    have hB : 0 ≤ R * Real.sin α / (4 * Real.pi) := by positivity
    calc Real.sin α / (24 * Real.pi) * N = R * Real.sin α / (4 * Real.pi) * ((N : ℝ) / (6 * R)) := by
          field_simp; ring
      _ ≤ ((Finset.Icc mlo mhi).card : ℝ) * ⌊(N : ℝ) / (3 * R)⌋₊ :=
          mul_le_mul (hA.trans hIcc) hfloor (by positivity) (by positivity)
  calc Real.sin α / (24 * Real.pi) * N ≤ _ := hfin
    _ ≤ (((Finset.Icc mlo mhi).biUnion T).card : ℝ) := by exact_mod_cast hsum
    _ ≤ _ := by exact_mod_cast Finset.card_le_card hgood

/-! ## Exponentials on the sampled circle -/

theorem unitRoot_pow_toNat_emod {N : ℕ} (hN : 0 < N) (n : ℤ) :
    unitRoot N ^ ((n % (N : ℤ)).toNat) = Complex.exp (2 * Real.pi * Complex.I * n / N) := by
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hnn : 0 ≤ n % (N : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hN.ne')
  unfold unitRoot
  rw [← Complex.exp_nat_mul]
  have hcast : (((n % (N : ℤ)).toNat : ℕ) : ℂ) = ((n % (N : ℤ) : ℤ) : ℂ) := by
    rw [← Int.toNat_of_nonneg hnn]; norm_cast
  rw [hcast, Int.emod_def]
  push_cast
  have : ((n : ℂ) - (N : ℂ) * ((n / (N : ℤ) : ℤ) : ℂ)) * (2 * Real.pi * Complex.I / N) =
      2 * Real.pi * Complex.I * n / N + (-(n / (N : ℤ)) : ℤ) * (2 * Real.pi * Complex.I) := by
    push_cast; field_simp; ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem re_mul_exp_ofReal_mul_I (B : ℂ) (x : ℝ) :
    (B * Complex.exp (x * Complex.I)).re = ‖B‖ * Real.cos (x + Complex.arg B) := by
  conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I B]
  rw [mul_assoc, ← Complex.exp_add, ← add_mul, show (B.arg : ℂ) + x = ((B.arg + x : ℝ) : ℂ) by
    push_cast; ring, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re, add_comm]

/-- The arc parameter `α = κ/4`. -/
def rotArc (κ : ℝ) : ℝ := κ / 4

/-- The fraction `sin α/(24π)`. -/
def rotFrac (κ : ℝ) : ℝ := Real.sin (rotArc κ) / (24 * Real.pi)

/-- The radius threshold. -/
def rotRadius (β κ M W₀ : ℝ) : ℝ :=
  16 * Real.pi / Real.sin (rotArc κ) + 8 / (5 * κ) * Real.log (4 * M / β + 1) +
    2 * Real.log (4 * (W₀ + 1) / β + 1) + 1

theorem rotArc_pos {κ : ℝ} (hκ : 0 < κ) : 0 < rotArc κ := by unfold rotArc; positivity

theorem sin_rotArc_pos {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) : 0 < Real.sin (rotArc κ) :=
  Real.sin_pos_of_pos_of_lt_pi (rotArc_pos hκ) (by unfold rotArc; linarith [Real.pi_gt_three])

theorem rotFrac_pos {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) : 0 < rotFrac κ := by
  unfold rotFrac; have := sin_rotArc_pos hκ hκ1; positivity

/-- `Re(B e^{R e^{iφ}}) = e^{R cos φ} |B| cos(R sin φ + arg B)`. -/
theorem re_mul_exp_polar (B : ℂ) (R φ : ℝ) :
    (B * Complex.exp ((R : ℂ) * Complex.exp ((φ : ℂ) * Complex.I))).re =
      Real.exp (R * Real.cos φ) * (‖B‖ * Real.cos (R * Real.sin φ + Complex.arg B)) := by
  have h : (R : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) =
      ((R * Real.cos φ : ℝ) : ℂ) + ((R * Real.sin φ : ℝ) : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]; push_cast; ring
  rw [h, Complex.exp_add, ← Complex.ofReal_exp, mul_left_comm, Complex.re_ofReal_mul,
    re_mul_exp_ofReal_mul_I]

/-- The non-dominant frequencies are exponentially smaller on the arc. -/
theorem norm_exp_nondominant_le {g₀ h ξ : ℂ} {R φ κ : ℝ} (hR : 0 ≤ R) (hφ0 : 0 ≤ φ)
    (hφα : φ ≤ κ / 4) (hh : ‖h‖ = 1) (hsep : h.re ≤ 1 - κ)
    (hg₀ξ : g₀ * ξ = (R : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)) :
    ‖Complex.exp (h * (g₀ * ξ))‖ ≤ Real.exp (R * (1 - 3 * κ / 4)) := by
  rw [Complex.norm_exp, hg₀ξ]
  refine Real.exp_le_exp.mpr ?_
  rw [show h * ((R : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)) =
    (R : ℂ) * (h * Complex.exp ((φ : ℂ) * Complex.I)) by ring, Complex.re_ofReal_mul]
  refine mul_le_mul_of_nonneg_left ?_ hR
  have h1 : (h * Complex.exp ((φ : ℂ) * Complex.I)).re =
      h.re + (h * (Complex.exp ((φ : ℂ) * Complex.I) - 1)).re := by
    rw [mul_sub, mul_one, Complex.sub_re]; ring
  have h2 : (h * (Complex.exp ((φ : ℂ) * Complex.I) - 1)).re ≤ φ := by
    refine (Complex.re_le_norm _).trans ?_
    rw [norm_mul, hh, one_mul, mul_comm]
    have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := φ)
    rw [Real.norm_eq_abs, abs_of_nonneg hφ0] at this
    exact this
  linarith

/-- **Negativity at one good sample.** -/
theorem neg_at_good_sample {S : Type*} [Fintype S] (g b : S → ℂ) (g₀ : ℂ)
    (hg : ∀ s, ‖g s‖ = 1) (hg₀ : ‖g₀‖ = 1) {β κ M W₀ : ℝ} (hβ : 0 < β) (hκ : 0 < κ)
    (hκ1 : κ ≤ 1) (hW₀ : 0 ≤ W₀)
    (hB : β ≤ ‖∑ s ∈ Finset.univ.filter (fun s => g s = g₀), b s‖)
    (hsep : ∀ s, g s ≠ g₀ → (g s * conj g₀).re ≤ 1 - κ) (hM : ∑ s, ‖b s‖ ≤ M)
    {R φ : ℝ} (hR : 0 < R) (hRM : Real.log (4 * M / β + 1) ≤ 5 * κ / 8 * R)
    (hRW : 2 * Real.log (4 * (W₀ + 1) / β + 1) < R) (hφ0 : 0 ≤ φ) (hφα : φ ≤ κ / 4)
    {ξ : ℂ} (hg₀ξ : g₀ * ξ = (R : ℂ) * Complex.exp ((φ : ℂ) * Complex.I))
    (hcos : Real.cos (R * Real.sin φ +
      Complex.arg (∑ s ∈ Finset.univ.filter (fun s => g s = g₀), b s)) ≤ -1 / 2)
    {L e : ℝ} (hL : |L| ≤ W₀) (he : |e| ≤ 1) :
    L + (∑ s, b s * Complex.exp (g s * ξ)).re + e < 0 := by
  set B₀ := ∑ s ∈ Finset.univ.filter (fun s => g s = g₀), b s with hB₀
  have hM0 : 0 ≤ M := le_trans (Finset.sum_nonneg fun s _ => norm_nonneg _) hM
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset S)
    (fun s => g s = g₀) (fun s => b s * Complex.exp (g s * ξ))
  have hdom : ∑ s ∈ Finset.univ.filter (fun s => g s = g₀), b s * Complex.exp (g s * ξ) =
      B₀ * Complex.exp (g₀ * ξ) := by
    rw [hB₀, Finset.sum_mul]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [(Finset.mem_filter.mp hs).2]
  have hcosφ : 1 - κ / 8 ≤ Real.cos φ := by
    have := Real.one_sub_sq_div_two_le_cos (x := φ)
    have : φ ^ 2 ≤ (κ / 4) ^ 2 := by gcongr
    nlinarith
  have hdomle : (B₀ * Complex.exp (g₀ * ξ)).re ≤ -(β / 2) * Real.exp (R * Real.cos φ) := by
    rw [hg₀ξ, re_mul_exp_polar]
    have hE := Real.exp_pos (R * Real.cos φ)
    have : ‖B₀‖ * Real.cos (R * Real.sin φ + Complex.arg B₀) ≤ -(β / 2) := by
      nlinarith [norm_nonneg B₀]
    nlinarith
  have hconj : conj g₀ * g₀ = 1 := by rw [Complex.conj_mul', hg₀]; simp
  have hrest : ‖∑ s ∈ Finset.univ.filter (fun s => ¬ g s = g₀), b s * Complex.exp (g s * ξ)‖ ≤
      M * Real.exp (R * (1 - 3 * κ / 4)) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ s ∈ Finset.univ.filter (fun s => ¬ g s = g₀), ‖b s * Complex.exp (g s * ξ)‖
        ≤ ∑ s ∈ Finset.univ.filter (fun s => ¬ g s = g₀),
            ‖b s‖ * Real.exp (R * (1 - 3 * κ / 4)) := by
          refine Finset.sum_le_sum fun s hs => ?_
          have hne := (Finset.mem_filter.mp hs).2
          rw [norm_mul]
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          have hgs : g s * ξ = (g s * conj g₀) * (g₀ * ξ) := by
            calc g s * ξ = g s * (conj g₀ * g₀) * ξ := by rw [hconj, mul_one]
              _ = _ := by ring
          rw [hgs]
          refine norm_exp_nondominant_le hR.le hφ0 hφα ?_ (hsep s hne) hg₀ξ
          rw [norm_mul, Complex.norm_conj, hg s, hg₀, mul_one]
      _ ≤ M * Real.exp (R * (1 - 3 * κ / 4)) := by
          rw [← Finset.sum_mul]
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun s _ _ => norm_nonneg _)) hM
  have hMle : M ≤ β / 4 * Real.exp (5 * κ / 8 * R) := by
    have h1 : 4 * M / β + 1 ≤ Real.exp (5 * κ / 8 * R) := by
      rw [← Real.exp_log (by positivity : 0 < 4 * M / β + 1)]
      exact Real.exp_le_exp.mpr hRM
    have h2 : 4 * M / β ≤ Real.exp (5 * κ / 8 * R) := by linarith
    rw [div_le_iff₀ hβ] at h2
    linarith
  have hsmall : M * Real.exp (R * (1 - 3 * κ / 4)) ≤ β / 4 * Real.exp (R * Real.cos φ) := by
    calc M * Real.exp (R * (1 - 3 * κ / 4)) ≤
        β / 4 * Real.exp (5 * κ / 8 * R) * Real.exp (R * (1 - 3 * κ / 4)) :=
          mul_le_mul_of_nonneg_right hMle (Real.exp_pos _).le
      _ = β / 4 * Real.exp (R * (1 - κ / 8)) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring
      _ ≤ β / 4 * Real.exp (R * Real.cos φ) := by gcongr
  have hsum : (∑ s, b s * Complex.exp (g s * ξ)).re ≤ -(β / 4) * Real.exp (R * Real.cos φ) := by
    rw [← hsplit, Complex.add_re, hdom]
    have := Complex.re_le_norm (∑ s ∈ Finset.univ.filter (fun s => ¬ g s = g₀),
      b s * Complex.exp (g s * ξ))
    linarith
  have hcos_half : R / 2 ≤ R * Real.cos φ := by nlinarith
  have hbig : W₀ + 1 < β / 4 * Real.exp (R * Real.cos φ) := by
    have h1 : 4 * (W₀ + 1) / β + 1 < Real.exp (R / 2) := by
      rw [← Real.exp_log (by positivity : 0 < 4 * (W₀ + 1) / β + 1)]
      exact Real.exp_lt_exp.mpr (by linarith)
    have h2 : 4 * (W₀ + 1) / β < Real.exp (R * Real.cos φ) :=
      lt_of_lt_of_le (by linarith) (Real.exp_le_exp.mpr hcos_half)
    rw [div_lt_iff₀ hβ] at h2
    linarith
  have hLabs := (abs_le.mp hL).2
  have heabs := (abs_le.mp he).2
  linarith

/-- **Sample angles.**  The rotated samples `g₀ ω^{j(t)} ζ` run through `|ζ| e^{i(φ₀ + 2πt/N)}`
with `0 ≤ φ₀ < 2π/N`, along an index map injective on `t < N`. -/
theorem exists_sample_angles {N : ℕ} (hN : 0 < N) (g₀ ζ : ℂ) (hg₀ : ‖g₀‖ = 1) :
    ∃ φ₀ : ℝ, 0 ≤ φ₀ ∧ φ₀ < 2 * Real.pi / N ∧ ∃ jmap : ℕ → Fin N,
      Set.InjOn jmap ↑(Finset.range N) ∧ ∀ t : ℕ,
        g₀ * (unitRoot N ^ ((jmap t : Fin N) : ℕ) * ζ) =
          ((‖ζ‖ : ℝ) : ℂ) * Complex.exp (((φ₀ + 2 * Real.pi * t / N : ℝ) : ℂ) * Complex.I) := by
  have hπ := Real.pi_pos
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set θ := Complex.arg (g₀ * ζ) with hθ
  have hg₀ζ : g₀ * ζ = ((‖ζ‖ : ℝ) : ℂ) * Complex.exp (θ * Complex.I) := by
    have := Complex.norm_mul_exp_arg_mul_I (g₀ * ζ)
    rw [norm_mul, hg₀, one_mul] at this
    exact this.symm
  set t₀ : ℤ := ⌈-θ * N / (2 * Real.pi)⌉ with ht₀
  refine ⟨θ + 2 * Real.pi * t₀ / N, ?_, ?_, ?_⟩
  · have h := Int.le_ceil (-θ * N / (2 * Real.pi))
    rw [← ht₀, div_le_iff₀ (by positivity)] at h
    have : -θ ≤ 2 * Real.pi * t₀ / N := by rw [le_div_iff₀ hNpos]; linarith
    linarith
  · have h := Int.ceil_lt_add_one (-θ * N / (2 * Real.pi))
    rw [← ht₀] at h
    have h' : (t₀ : ℝ) - 1 < -θ * N / (2 * Real.pi) := by linarith
    rw [lt_div_iff₀ (by positivity)] at h'
    have : 2 * Real.pi * t₀ / N < -θ + 2 * Real.pi / N := by
      rw [div_lt_iff₀ hNpos, add_mul, div_mul_cancel₀ _ hNpos.ne']; linarith
    linarith
  have hN0 : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  have hNz : (0 : ℤ) < N := by exact_mod_cast hN
  refine ⟨fun t => ⟨((t₀ + t) % (N : ℤ)).toNat, by
    have h0 : 0 ≤ (t₀ + t) % (N : ℤ) := Int.emod_nonneg _ hN0
    have h1 : (t₀ + t) % (N : ℤ) < N := Int.emod_lt_of_pos _ hNz
    omega⟩, ?_, ?_⟩
  · intro t ht t' ht' h
    simp only [Finset.coe_range, Set.mem_Iio] at ht ht'
    have hv := congrArg Fin.val h
    simp only at hv
    have h0 : 0 ≤ (t₀ + t) % (N : ℤ) := Int.emod_nonneg _ hN0
    have h0' : 0 ≤ (t₀ + t') % (N : ℤ) := Int.emod_nonneg _ hN0
    have hz : (t₀ + t) % (N : ℤ) = (t₀ + t') % (N : ℤ) := by omega
    have hmod : (t₀ + (t : ℤ)) ≡ t₀ + t' [ZMOD N] := hz
    obtain ⟨k, hk⟩ := (Int.ModEq.add_left_cancel' t₀ hmod).dvd
    have htt : (t : ℤ) < N := by exact_mod_cast ht
    have htt' : (t' : ℤ) < N := by exact_mod_cast ht'
    have hk0 : k = 0 := by
      rcases lt_trichotomy k 0 with hk1 | hk1 | hk1
      · have : (N : ℤ) * k ≤ -N := by nlinarith
        omega
      · exact hk1
      · have : (N : ℤ) ≤ (N : ℤ) * k := by nlinarith
        omega
    rw [hk0, mul_zero] at hk
    omega
  · intro t
    have hpow : unitRoot N ^ (((t₀ + t) % (N : ℤ)).toNat) =
        Complex.exp (2 * Real.pi * Complex.I * ((t₀ + t : ℤ) : ℂ) / N) :=
      unitRoot_pow_toNat_emod hN (t₀ + t)
    simp only
    rw [show g₀ * (unitRoot N ^ (((t₀ + t) % (N : ℤ)).toNat) * ζ) =
      unitRoot N ^ (((t₀ + t) % (N : ℤ)).toNat) * (g₀ * ζ) by ring, hg₀ζ, hpow,
      mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast; field_simp; ring

/-- **Rotation lemma.** -/
theorem card_rotation_negative {S : Type*} [Fintype S] (g b : S → ℂ) (g₀ : ℂ)
    (hg : ∀ s, ‖g s‖ = 1) (hg₀ : ‖g₀‖ = 1) {β κ M W₀ : ℝ} (hβ : 0 < β) (hκ : 0 < κ)
    (hκ1 : κ ≤ 1) (hW₀ : 0 ≤ W₀)
    (hB : β ≤ ‖∑ s ∈ Finset.univ.filter (fun s => g s = g₀), b s‖)
    (hsep : ∀ s, g s ≠ g₀ → (g s * conj g₀).re ≤ 1 - κ) (hM : ∑ s, ‖b s‖ ≤ M)
    {R₁ : ℝ} {N : ℕ} (hN : 6 * R₁ + 2 ≤ N) {ζ : ℂ} (hζ0 : rotRadius β κ M W₀ ≤ ‖ζ‖)
    (hζ1 : ‖ζ‖ ≤ R₁) {L : ℝ} (hL : |L| ≤ W₀) (e : Fin N → ℝ) (he : ∀ j, |e j| ≤ 1) :
    rotFrac κ * N ≤ ((Finset.univ.filter fun j : Fin N =>
      L + (∑ s, b s * Complex.exp (g s * (unitRoot N ^ (j : ℕ) * ζ))).re + e j < 0).card : ℝ) := by
  have hπ := Real.pi_pos
  have hα0 := rotArc_pos hκ
  have hα1 : rotArc κ ≤ 1 / 4 := by unfold rotArc; linarith
  have hαπ : rotArc κ ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
  have hsinα := sin_rotArc_pos hκ hκ1
  have hM0 : 0 ≤ M := le_trans (Finset.sum_nonneg fun s _ => norm_nonneg _) hM
  have hlog1 : 0 ≤ Real.log (4 * M / β + 1) := Real.log_nonneg (by
    have : 0 ≤ 4 * M / β := by positivity
    linarith)
  have hlog2 : 0 ≤ Real.log (4 * (W₀ + 1) / β + 1) := Real.log_nonneg (by
    have : 0 ≤ 4 * (W₀ + 1) / β := by positivity
    linarith)
  set R := ‖ζ‖ with hRdef
  have hR16 : 16 * Real.pi / Real.sin (rotArc κ) ≤ R := by
    have : 0 ≤ 8 / (5 * κ) * Real.log (4 * M / β + 1) := by positivity
    unfold rotRadius at hζ0; linarith
  have hRpos : 0 < R := lt_of_lt_of_le (by positivity) hR16
  have hRα : 16 * Real.pi ≤ R * Real.sin (rotArc κ) := by
    rw [div_le_iff₀ hsinα] at hR16; linarith
  have hRM : Real.log (4 * M / β + 1) ≤ 5 * κ / 8 * R := by
    have h1 : 8 / (5 * κ) * Real.log (4 * M / β + 1) ≤ R := by
      have : 0 ≤ 16 * Real.pi / Real.sin (rotArc κ) := by positivity
      unfold rotRadius at hζ0; linarith
    have h2 : 8 / (5 * κ) * Real.log (4 * M / β + 1) * (5 * κ / 8) =
        Real.log (4 * M / β + 1) := by field_simp
    nlinarith
  have hRW : 2 * Real.log (4 * (W₀ + 1) / β + 1) < R := by
    have : 0 ≤ 16 * Real.pi / Real.sin (rotArc κ) + 8 / (5 * κ) * Real.log (4 * M / β + 1) := by
      positivity
    unfold rotRadius at hζ0; linarith
  have hNpos : (0 : ℝ) < N := by
    have : 0 ≤ R₁ := le_trans hRpos.le hζ1
    linarith
  have hN0 : 0 < N := by exact_mod_cast hNpos
  have hN6 : 6 * R ≤ N := by linarith
  obtain ⟨φ₀, hφ₀0, hφ₀N, jmap, hjinj, hsample⟩ := exists_sample_angles hN0 g₀ ζ hg₀
  set B₀ := ∑ s ∈ Finset.univ.filter (fun s => g s = g₀), b s with hB₀
  set G := (Finset.range N).filter (fun t : ℕ => φ₀ + 2 * Real.pi * t / N ≤ rotArc κ ∧
      Real.cos (R * Real.sin (φ₀ + 2 * Real.pi * t / N) + Complex.arg B₀) ≤ -1 / 2) with hG
  have hgood : Real.sin (rotArc κ) / (24 * Real.pi) * N ≤ (G.card : ℝ) :=
    card_good_samples hRpos hα0 hαπ hφ₀0 hφ₀N hN6 hRα
  have himage : G.image jmap ⊆ Finset.univ.filter fun j : Fin N =>
      L + (∑ s, b s * Complex.exp (g s * (unitRoot N ^ (j : ℕ) * ζ))).re + e j < 0 := by
    intro j hj
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hj
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have ht' := Finset.mem_filter.mp ht
    have hφ0 : 0 ≤ φ₀ + 2 * Real.pi * t / N := by
      have : 0 ≤ 2 * Real.pi * t / N := by positivity
      linarith
    exact neg_at_good_sample g b g₀ hg hg₀ hβ hκ hκ1 hW₀ hB hsep hM hRpos hRM hRW hφ0
      (by have := ht'.2.1; unfold rotArc at this; exact this) (hsample t) ht'.2.2 hL (he _)
  have hinjG : Set.InjOn jmap ↑G := hjinj.mono (by
    intro t ht; exact Finset.mem_coe.mpr (Finset.mem_filter.mp ht).1)
  calc rotFrac κ * N = Real.sin (rotArc κ) / (24 * Real.pi) * N := by rw [rotFrac]
    _ ≤ (G.card : ℝ) := hgood
    _ = ((G.image jmap).card : ℝ) := by rw [Finset.card_image_of_injOn hinjG]
    _ ≤ _ := by exact_mod_cast Finset.card_le_card himage

end

end RHTower
