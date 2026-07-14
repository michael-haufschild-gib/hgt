import Mathlib
import GaloisForLFunctions.HTGeometry.ArchimedeanBendLaw

/-!
# Super-increasing valuation gap

For a nonnegative sequence `b` that is `(C+1)`-super-increasing
(`(C+1) · ∑_{n<k} b n ≤ b k`), the weighted sum `∑ g n · b n` of any nonzero integer sequence `g`
with entries bounded by `C` is bounded away from zero by `b K / (C+1)`, where `K` is the top index of
`g`'s support (`valuation_gap_of_superIncreasing`).

This is the numeral-system uniqueness underlying magnitude hypertranscendence: distinct convolution
atoms of a superlacunary Taylor-magnitude series have distinct valuations, separated by a gap that
grows with the scale.  It supplies the off-balanced-vs-off-balanced valuation separation that the
balanced-atom estimates (`MagnitudeBalancedGap`) do not provide, letting the *minimal-valuation
appearing* atom dominate regardless of leading-symbol degeneracy.
-/

open Finset Filter Topology

namespace GaloisForLFunctions

/-- **Superlacunary implies super-increasing on a tail.**  If `b` is positive with successive ratios
tending to infinity, then for every bound `C` there is a threshold past which `b` is
`(C+1)`-super-increasing: `(C+1) · ∑_{n<k} b n ≤ b k`.  The tail of the partial sum is geometrically
dominated by its last term, and `b → ∞` absorbs the fixed head. -/
theorem exists_superIncreasing_of_ratio {b : ℕ → ℝ} (hbpos : ∀ n, 0 < b n)
    (hratio : Tendsto (fun n => b (n + 1) / b n) atTop atTop) (C : ℕ) :
    ∃ N₀, ∀ k, N₀ ≤ k → ((C : ℝ) + 1) * (∑ n ∈ Finset.range k, b n) ≤ b k := by
  obtain ⟨N₁, hN₁⟩ := (hratio.eventually_ge_atTop (3 * ((C : ℝ) + 1))).exists_forall_of_atTop
  have hstep : ∀ n, N₁ ≤ n → 3 * ((C : ℝ) + 1) * b n ≤ b (n + 1) := by
    intro n hn
    have h := hN₁ n hn
    rw [le_div_iff₀ (hbpos n)] at h
    linarith [h]
  have hgeo : ∀ j, ∑ n ∈ Finset.Ico N₁ (N₁ + j + 1), b n ≤ 2 * b (N₁ + j) := by
    intro j
    induction j with
    | zero =>
      simp only [Nat.add_zero, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left,
        Finset.sum_range_one, Nat.add_zero]
      linarith [hbpos N₁]
    | succ j ih =>
      have hsplit : ∑ n ∈ Finset.Ico N₁ (N₁ + j + 1 + 1), b n
          = (∑ n ∈ Finset.Ico N₁ (N₁ + j + 1), b n) + b (N₁ + j + 1) :=
        Finset.sum_Ico_succ_top (by omega) b
      have hs := hstep (N₁ + j) (by omega)
      have h2 : (2:ℝ) * b (N₁ + j) ≤ b (N₁ + j + 1) := by nlinarith [hbpos (N₁ + j)]
      rw [show N₁ + (j + 1) = N₁ + j + 1 by omega, hsplit]
      linarith [ih, h2]
  have hgrow : ∀ j, (2:ℝ) ^ j * b N₁ ≤ b (N₁ + j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hs := hstep (N₁ + j) (by omega)
      have h2 : (2:ℝ) * b (N₁ + j) ≤ b (N₁ + j + 1) := by nlinarith [hbpos (N₁ + j)]
      calc (2:ℝ) ^ (j + 1) * b N₁ = 2 * ((2:ℝ) ^ j * b N₁) := by ring
        _ ≤ 2 * b (N₁ + j) := by linarith [ih]
        _ ≤ b (N₁ + j + 1) := h2
        _ = b (N₁ + (j + 1)) := by congr 1
  set H := ∑ n ∈ Finset.range N₁, b n with hHdef
  have hpow : Tendsto (fun j => (2:ℝ) ^ j * b N₁) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (show (1:ℝ) < 2 by norm_num)).atTop_mul_const (hbpos N₁)
  obtain ⟨j₀, hj₀⟩ := (hpow.eventually_ge_atTop H).exists_forall_of_atTop
  refine ⟨N₁ + j₀ + 1, fun k hk => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, k = N₁ + m + 1 := ⟨k - N₁ - 1, by omega⟩
  have hmj₀ : j₀ ≤ m := by omega
  have hrangesplit : ∑ n ∈ Finset.range (N₁ + m + 1), b n
      = H + ∑ n ∈ Finset.Ico N₁ (N₁ + m + 1), b n := by
    rw [hHdef]
    exact (Finset.sum_range_add_sum_Ico b (show N₁ ≤ N₁ + m + 1 by omega)).symm
  have hHle : H ≤ b (N₁ + m) := le_trans (hj₀ m hmj₀) (hgrow m)
  have hgeom := hgeo m
  have hsm := hstep (N₁ + m) (by omega)
  rw [hrangesplit]
  calc ((C : ℝ) + 1) * (H + ∑ n ∈ Finset.Ico N₁ (N₁ + m + 1), b n)
      ≤ ((C : ℝ) + 1) * (b (N₁ + m) + 2 * b (N₁ + m)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity); linarith [hHle, hgeom]
    _ = 3 * ((C : ℝ) + 1) * b (N₁ + m) := by ring
    _ ≤ b (N₁ + m + 1) := hsm

/-- **Super-increasing valuation gap.**  If `b` is nonnegative and `(C+1)`-super-increasing, then for a
nonzero `g : ℕ →₀ ℤ` with `|g n| ≤ C`, the weighted valuation `∑ g n · b n` has absolute value at least
`b K / (C+1)`, where `K` is the greatest index in `g`'s support. -/
theorem valuation_gap_of_superIncreasing {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n) {C : ℕ}
    (hsi : ∀ k, ((C : ℝ) + 1) * (∑ n ∈ Finset.range k, b n) ≤ b k)
    {g : ℕ →₀ ℤ} (hg : ∀ n, (g n).natAbs ≤ C) (hg0 : g ≠ 0) :
    b (g.support.max' (Finsupp.support_nonempty_iff.mpr hg0)) / ((C : ℝ) + 1)
      ≤ |∑ n ∈ g.support, (g n : ℝ) * b n| := by
  classical
  set K := g.support.max' (Finsupp.support_nonempty_iff.mpr hg0) with hKdef
  have hKmem : K ∈ g.support := Finset.max'_mem _ _
  have hKle : ∀ n ∈ g.support, n ≤ K := fun n hn => Finset.le_max' _ _ hn
  have hsplit : ∑ n ∈ g.support, (g n : ℝ) * b n
      = (g K : ℝ) * b K + ∑ n ∈ g.support.erase K, (g n : ℝ) * b n :=
    (Finset.add_sum_erase _ _ hKmem).symm
  have hsub : g.support.erase K ⊆ Finset.range K := by
    intro n hn
    rw [Finset.mem_erase] at hn
    exact Finset.mem_range.mpr (lt_of_le_of_ne (hKle n hn.2) hn.1)
  have htail : |∑ n ∈ g.support.erase K, (g n : ℝ) * b n| ≤ (C : ℝ) * ∑ n ∈ Finset.range K, b n := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hbnd : ∀ n ∈ g.support.erase K, |(g n : ℝ) * b n| ≤ (C : ℝ) * b n := by
      intro n _
      rw [abs_mul, abs_of_nonneg (hb n)]
      have hle : |(g n : ℝ)| ≤ (C : ℝ) := by
        have hz : (|g n| : ℤ) ≤ (C : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast hg n
        rw [← Int.cast_abs]; exact_mod_cast hz
      exact mul_le_mul_of_nonneg_right hle (hb n)
    refine le_trans (Finset.sum_le_sum hbnd) ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hb n)
  have hgK1 : (1 : ℝ) ≤ |(g K : ℝ)| := by
    have hne : g K ≠ 0 := Finsupp.mem_support_iff.mp hKmem
    have hz : (1 : ℤ) ≤ |g K| := by rw [Int.abs_eq_natAbs]; exact_mod_cast Int.natAbs_pos.mpr hne
    rw [← Int.cast_abs]; exact_mod_cast hz
  have hsiK := hsi K
  have hbK : 0 ≤ b K := hb K
  rw [hsplit]
  have hrev := abs_sub_abs_le_abs_add ((g K : ℝ) * b K)
      (∑ n ∈ g.support.erase K, (g n : ℝ) * b n)
  have habsGK : |(g K : ℝ) * b K| = |(g K : ℝ)| * b K := by rw [abs_mul, abs_of_nonneg hbK]
  have hsum_le : ∑ n ∈ Finset.range K, b n ≤ b K / ((C:ℝ)+1) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith [hsiK]
  have hstep : b K / ((C : ℝ) + 1) ≤ |(g K : ℝ)| * b K
      - |∑ n ∈ g.support.erase K, (g n : ℝ) * b n| := by
    have h1 : (C : ℝ) * ∑ n ∈ Finset.range K, b n ≤ (C : ℝ) / ((C:ℝ)+1) * b K := by
      rw [div_mul_eq_mul_div, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hsum_le (by positivity)
    have h2 : b K ≤ |(g K : ℝ)| * b K := by
      calc b K = 1 * b K := (one_mul _).symm
        _ ≤ |(g K : ℝ)| * b K := mul_le_mul_of_nonneg_right hgK1 hbK
    have h3 : b K - (C : ℝ) / ((C:ℝ)+1) * b K = b K / ((C:ℝ)+1) := by field_simp; ring
    linarith [htail]
  linarith [hrev, hstep, habsGK]

/-- **Minimal-valuation domination.**  A finite integer-weighted sum `∑ c_i · a_i` of complex atoms
with prescribed magnitudes `‖a_i‖ = exp(−V_i)` is nonzero when one index `i₀` has nonzero weight and
strictly minimal valuation, separated from the rest by a gap `G` exceeding `log ∑|c_i|`. -/
theorem weighted_sum_ne_zero_of_min_valuation {ι : Type*} [DecidableEq ι] (s : Finset ι) (V : ι → ℝ)
    (a : ι → ℂ) (ha : ∀ i, ‖a i‖ = Real.exp (- V i)) (c : ι → ℤ) {i₀ : ι} (hi₀ : i₀ ∈ s)
    (hc : c i₀ ≠ 0) {G : ℝ} (hgap : ∀ i ∈ s.erase i₀, V i₀ + G ≤ V i)
    (hG : (∑ i ∈ s, (|c i| : ℝ)) < Real.exp G) :
    ∑ i ∈ s, (c i : ℂ) * a i ≠ 0 := by
  apply sum_ne_zero_of_dominant s c a hi₀ hc
  rw [ha i₀]
  have hstep : ∑ i ∈ s.erase i₀, ‖(c i : ℂ) * a i‖
      ≤ (∑ i ∈ s.erase i₀, (|c i| : ℝ)) * Real.exp (- V i₀ - G) := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    rw [norm_mul, Complex.norm_intCast, ha i]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    apply Real.exp_le_exp.mpr
    have := hgap i hi
    linarith
  refine lt_of_le_of_lt hstep ?_
  rw [show (- V i₀ - G) = (- V i₀) + (- G) by ring, Real.exp_add,
    ← mul_assoc, mul_comm _ (Real.exp (-V i₀))]
  have hpos : (0:ℝ) < Real.exp (- V i₀) := Real.exp_pos _
  rw [mul_assoc]
  refine (mul_lt_iff_lt_one_right hpos).mpr ?_
  have h1 : (∑ i ∈ s.erase i₀, (|c i| : ℝ)) ≤ ∑ i ∈ s, (|c i| : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun i _ _ => by positivity)
  calc (∑ i ∈ s.erase i₀, (|c i| : ℝ)) * Real.exp (-G)
      ≤ (∑ i ∈ s, (|c i| : ℝ)) * Real.exp (-G) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ < Real.exp G * Real.exp (-G) := mul_lt_mul_of_pos_right hG (Real.exp_pos _)
    _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]

/-- The **index-multiset** of a `Fin D`-tuple: `key h n` counts the coordinates hitting `n`. -/
noncomputable def key {D : ℕ} (h : Fin D → ℕ) : ℕ →₀ ℕ := ∑ t, Finsupp.single (h t) 1

/-- The valuation of a tuple is the key-weighted sum of `b`. -/
theorem valuation_eq_key_sum {D : ℕ} (h : Fin D → ℕ) (b : ℕ → ℝ) :
    (key h).sum (fun n k => (k : ℝ) * b n) = ∑ t, b (h t) := by
  rw [key, ← Finsupp.sum_finsetSum_index (by intro i; simp) (by intro i k₁ k₂; push_cast; ring)]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [Finsupp.sum_single_index (by simp)]
  simp

/-- Each key entry is at most the tuple arity `D`. -/
theorem key_apply_le {D : ℕ} (h : Fin D → ℕ) (n : ℕ) : (key h) n ≤ D := by
  rw [key, Finsupp.finsetSum_apply]
  calc ∑ t, (Finsupp.single (h t) 1) n ≤ ∑ _t : Fin D, 1 := by
        apply Finset.sum_le_sum; intro t _
        rw [Finsupp.single_apply]; split <;> simp
    _ = D := by simp

/-- A product over a tuple equals the key-weighted product: coordinates hitting `n` contribute
`g n` each, so the whole product is `∏ₙ (g n)^{key n}`.  This factors the common atom value out of a
same-multiset fiber. -/
theorem prod_eq_key_prod {D : ℕ} (h : Fin D → ℕ) {M : Type*} [CommMonoid M] (g : ℕ → M) :
    (key h).prod (fun n k => (g n) ^ k) = ∏ t, g (h t) := by
  rw [key, ← Finsupp.prod_finsetSum_index (by intro i; simp) (by intro i k₁ k₂; rw [pow_add])]
  refine Finset.prod_congr rfl (fun t _ => ?_)
  rw [Finsupp.prod_single_index (by simp)]
  simp

/-- **Pairwise valuation gap.**  Two distinct `≤ D`-bounded multi-indices have valuations
`V(ν) = ∑ₙ ν n·b n` separated by at least `b K / (D+1)` for some index `K` (the top index where they
differ), under a `(D+1)`-super-increasing profile `b`.  This is the gap feeding the minimal-atom
domination in the magnitude-lacunary survival argument. -/
theorem finsupp_pair_valuation_gap {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n) {D : ℕ}
    (hsi : ∀ k, ((D : ℝ) + 1) * (∑ n ∈ Finset.range k, b n) ≤ b k)
    {ν ν' : ℕ →₀ ℕ} (hν : ∀ n, ν n ≤ D) (hν' : ∀ n, ν' n ≤ D) (hne : ν ≠ ν') :
    ∃ K : ℕ, b K / ((D : ℝ) + 1)
      ≤ |ν.sum (fun n k => (k : ℝ) * b n) - ν'.sum (fun n k => (k : ℝ) * b n)| := by
  classical
  set g : ℕ →₀ ℤ := ν.mapRange (Nat.cast : ℕ → ℤ) Nat.cast_zero
    - ν'.mapRange (Nat.cast : ℕ → ℤ) Nat.cast_zero
    with hg
  have hgn : ∀ n, g n = (ν n : ℤ) - (ν' n : ℤ) := by
    intro n; rw [hg]; simp [Finsupp.sub_apply, Finsupp.mapRange_apply]
  have hgbound : ∀ n, (g n).natAbs ≤ D := by
    intro n; rw [hgn]; have h1 := hν n; have h2 := hν' n; omega
  have hg0 : g ≠ 0 := by
    intro h0
    apply hne
    ext n
    have := hgn n
    rw [h0] at this
    simp at this
    omega
  -- valuation difference equals ∑ g_n b_n
  have hsupp : g.support ⊆ ν.support ∪ ν'.support := by
    intro n hn
    rw [Finsupp.mem_support_iff, hgn] at hn
    simp only [Finset.mem_union, Finsupp.mem_support_iff]
    by_contra hc
    push_neg at hc
    rw [hc.1, hc.2] at hn
    simp at hn
  have hval : ∑ n ∈ g.support, (g n : ℝ) * b n
      = ν.sum (fun n k => (k : ℝ) * b n) - ν'.sum (fun n k => (k : ℝ) * b n) := by
    rw [Finsupp.sum, Finsupp.sum]
    rw [Finset.sum_subset (Finset.subset_union_left (s₁ := ν.support) (s₂ := ν'.support))
      (fun n _ hn => by rw [Finsupp.notMem_support_iff.mp hn]; simp)]
    rw [Finset.sum_subset (Finset.subset_union_right (s₁ := ν.support) (s₂ := ν'.support))
      (fun n _ hn => by rw [Finsupp.notMem_support_iff.mp hn]; simp)]
    rw [Finset.sum_subset hsupp (fun n _ hn => by
      rw [Finsupp.notMem_support_iff.mp hn]; simp), ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    rw [hgn]; push_cast; ring
  have hgap := valuation_gap_of_superIncreasing hb hsi hgbound hg0
  refine ⟨g.support.max' (Finsupp.support_nonempty_iff.mpr hg0), ?_⟩
  rw [← hval]
  exact hgap

/-- **Uniform valuation gap.**  A finite nonempty family of `≤ D`-bounded multi-indices has a
minimal-valuation element `ν₀` and a strictly positive gap `G` below every other member's valuation
— the finite minimum of the pairwise gaps.  Discharges the `hgap` hypothesis of the survival
criterion. -/
theorem exists_uniform_valuation_gap {b : ℕ → ℝ} (hbpos : ∀ n, 0 < b n) {D : ℕ}
    (hsi : ∀ k, ((D : ℝ) + 1) * (∑ n ∈ Finset.range k, b n) ≤ b k)
    (K : Finset (ℕ →₀ ℕ)) (hKbound : ∀ ν ∈ K, ∀ n, ν n ≤ D) (hKne : K.Nonempty) :
    ∃ ν₀ ∈ K, ∃ G : ℝ, 0 < G ∧ ∀ ν ∈ K.erase ν₀,
      ν₀.sum (fun n k => (k : ℝ) * b n) + G ≤ ν.sum (fun n k => (k : ℝ) * b n) := by
  classical
  obtain ⟨ν₀, hν₀K, hν₀min⟩ :=
    K.exists_min_image (fun ν => ν.sum (fun n k => (k : ℝ) * b n)) hKne
  refine ⟨ν₀, hν₀K, ?_⟩
  rcases (K.erase ν₀).eq_empty_or_nonempty with he | hne
  · exact ⟨1, one_pos, fun ν hν => absurd hν (he ▸ Finset.notMem_empty ν)⟩
  · obtain ⟨ν₁, hν₁, hν₁min⟩ := (K.erase ν₀).exists_min_image
      (fun ν => ν.sum (fun n k => (k : ℝ) * b n) - ν₀.sum (fun n k => (k : ℝ) * b n)) hne
    have hgap1 : 0 < ν₁.sum (fun n k => (k : ℝ) * b n) - ν₀.sum (fun n k => (k : ℝ) * b n) := by
      have hne' : ν₁ ≠ ν₀ := (Finset.mem_erase.mp hν₁).1
      obtain ⟨Kidx, hKidx⟩ := finsupp_pair_valuation_gap (fun n => (hbpos n).le) hsi
        (hKbound ν₁ (Finset.mem_of_mem_erase hν₁)) (hKbound ν₀ hν₀K) hne'
      have hpos : 0 < b Kidx / ((D : ℝ) + 1) := by
        have := hbpos Kidx; positivity
      have hge : ν₀.sum (fun n k => (k : ℝ) * b n) ≤ ν₁.sum (fun n k => (k : ℝ) * b n) :=
        hν₀min ν₁ (Finset.mem_of_mem_erase hν₁)
      rw [abs_of_nonneg (by linarith)] at hKidx
      linarith
    refine ⟨ν₁.sum (fun n k => (k : ℝ) * b n) - ν₀.sum (fun n k => (k : ℝ) * b n), hgap1,
      fun ν hν => ?_⟩
    have := hν₁min ν hν
    linarith

/-- **Single-atom valuation levels.**  Under a `(D+1)`-super-increasing positive profile `b`,
distinct `≤ D`-bounded multi-indices have distinct valuations: `V` is injective on them.  Hence the
minimal-valuation appearing atom is unique — the structural fact that makes the leading-symbol
degeneracy irrelevant in magnitude-lacunary survival. -/
theorem valuation_injOn {b : ℕ → ℝ} (hbpos : ∀ n, 0 < b n) {D : ℕ}
    (hsi : ∀ k, ((D : ℝ) + 1) * (∑ n ∈ Finset.range k, b n) ≤ b k)
    {ν ν' : ℕ →₀ ℕ} (hν : ∀ n, ν n ≤ D) (hν' : ∀ n, ν' n ≤ D)
    (hV : ν.sum (fun n k => (k : ℝ) * b n) = ν'.sum (fun n k => (k : ℝ) * b n)) :
    ν = ν' := by
  by_contra hne
  obtain ⟨K, hK⟩ := finsupp_pair_valuation_gap (fun n => (hbpos n).le) hsi hν hν' hne
  rw [hV, sub_self, abs_zero] at hK
  have hpos : 0 < b K / ((D : ℝ) + 1) := by have := hbpos K; positivity
  linarith

theorem sum_ne_zero_of_dominant_complex {ι : Type*} [DecidableEq ι] (s : Finset ι) (w : ι → ℂ)
    {i₀ : ι} (hi₀ : i₀ ∈ s) (hdom : ∑ i ∈ s.erase i₀, ‖w i‖ < ‖w i₀‖) :
    ∑ i ∈ s, w i ≠ 0 := by
  rw [← Finset.add_sum_erase s w hi₀]
  intro heq
  have h1 : w i₀ = -(∑ i ∈ s.erase i₀, w i) := eq_neg_of_add_eq_zero_left heq
  have h2 : ‖w i₀‖ ≤ ∑ i ∈ s.erase i₀, ‖w i‖ := by
    rw [h1, norm_neg]; exact norm_sum_le _ _
  linarith

/-- **Complex minimal-valuation domination.**  The integer-weight version, extended to complex
coefficients `c : ι → ℂ`: the minimal-valuation atom `i₀` with nonzero coefficient dominates when the
total coefficient norm mass is below `‖c i₀‖·exp G`.  This is what closes magnitude-lacunary survival
for a general (complex-coefficient) algebraic differential relation, not just an integer one. -/
theorem weighted_sum_ne_zero_of_min_valuation_complex {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (V : ι → ℝ) (a : ι → ℂ) (ha : ∀ i, ‖a i‖ = Real.exp (- V i)) (c : ι → ℂ) {i₀ : ι}
    (hi₀ : i₀ ∈ s) (hc : c i₀ ≠ 0) {G : ℝ} (hgap : ∀ i ∈ s.erase i₀, V i₀ + G ≤ V i)
    (hG : (∑ i ∈ s, ‖c i‖) < ‖c i₀‖ * Real.exp G) :
    ∑ i ∈ s, c i * a i ≠ 0 := by
  apply sum_ne_zero_of_dominant_complex s (fun i => c i * a i) hi₀
  rw [norm_mul, ha i₀]
  have hstep : ∑ i ∈ s.erase i₀, ‖c i * a i‖
      ≤ (∑ i ∈ s.erase i₀, ‖c i‖) * Real.exp (- V i₀ - G) := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    rw [norm_mul, ha i]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    exact Real.exp_le_exp.mpr (by linarith [hgap i hi])
  refine lt_of_le_of_lt hstep ?_
  have hc0 : 0 < ‖c i₀‖ := norm_pos_iff.mpr hc
  have hpos : (0:ℝ) < Real.exp (- V i₀) := Real.exp_pos _
  rw [show (- V i₀ - G) = (- V i₀) + (- G) by ring, Real.exp_add]
  have h1 : (∑ i ∈ s.erase i₀, ‖c i‖) ≤ ∑ i ∈ s, ‖c i‖ :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun i _ _ => norm_nonneg _)
  have hkey : (∑ i ∈ s.erase i₀, ‖c i‖) * Real.exp (-G) < ‖c i₀‖ := by
    have : (∑ i ∈ s.erase i₀, ‖c i‖) * Real.exp (-G) ≤ (∑ i ∈ s, ‖c i‖) * Real.exp (-G) :=
      mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    have hlt : (∑ i ∈ s, ‖c i‖) * Real.exp (-G) < (‖c i₀‖ * Real.exp G) * Real.exp (-G) :=
      mul_lt_mul_of_pos_right hG (Real.exp_pos _)
    rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one] at hlt
    linarith
  calc (∑ i ∈ s.erase i₀, ‖c i‖) * (Real.exp (- V i₀) * Real.exp (- G))
      = ((∑ i ∈ s.erase i₀, ‖c i‖) * Real.exp (- G)) * Real.exp (- V i₀) := by ring
    _ < ‖c i₀‖ * Real.exp (- V i₀) := mul_lt_mul_of_pos_right hkey hpos

/-- Every index-multiset `key h` is `≤ D`-bounded. -/
theorem key_apply_bounded {D : ℕ} (h : Fin D → ℕ) : ∀ n, (key h) n ≤ D :=
  fun n => key_apply_le h n

theorem valuation_key_injOn {b : ℕ → ℝ} (hbpos : ∀ n, 0 < b n) {D : ℕ}
    (hsi : ∀ k, ((D : ℝ) + 1) * (∑ n ∈ Finset.range k, b n) ≤ b k)
    {h h' : Fin D → ℕ}
    (hV : (∑ t, b (h t)) = ∑ t, b (h' t)) : key h = key h' := by
  apply valuation_injOn hbpos hsi (key_apply_bounded h) (key_apply_bounded h')
  rw [valuation_eq_key_sum, valuation_eq_key_sum, hV]

/-- **Valuation gap from the top-index super-increasing bound alone.**  The gap estimate needs the
`(C+1)`-super-increasing inequality only at the top index `K = max' g.support` — enabling the
superlacunar (tail-super-increasing) regime, where the bound holds only for large indices. -/
theorem valuation_gap_of_hsi_at_max {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n) {C : ℕ}
    {g : ℕ →₀ ℤ} (hg : ∀ n, (g n).natAbs ≤ C) (hg0 : g ≠ 0)
    (hsiK : ((C : ℝ) + 1)
        * (∑ n ∈ Finset.range (g.support.max' (Finsupp.support_nonempty_iff.mpr hg0)), b n)
      ≤ b (g.support.max' (Finsupp.support_nonempty_iff.mpr hg0))) :
    b (g.support.max' (Finsupp.support_nonempty_iff.mpr hg0)) / ((C : ℝ) + 1)
      ≤ |∑ n ∈ g.support, (g n : ℝ) * b n| := by
  classical
  set K := g.support.max' (Finsupp.support_nonempty_iff.mpr hg0) with hKdef
  have hKmem : K ∈ g.support := Finset.max'_mem _ _
  have hKle : ∀ n ∈ g.support, n ≤ K := fun n hn => Finset.le_max' _ _ hn
  have hsplit : ∑ n ∈ g.support, (g n : ℝ) * b n
      = (g K : ℝ) * b K + ∑ n ∈ g.support.erase K, (g n : ℝ) * b n :=
    (Finset.add_sum_erase _ _ hKmem).symm
  have hsub : g.support.erase K ⊆ Finset.range K := by
    intro n hn; rw [Finset.mem_erase] at hn
    exact Finset.mem_range.mpr (lt_of_le_of_ne (hKle n hn.2) hn.1)
  have htail : |∑ n ∈ g.support.erase K, (g n : ℝ) * b n| ≤ (C : ℝ) * ∑ n ∈ Finset.range K, b n := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hbnd : ∀ n ∈ g.support.erase K, |(g n : ℝ) * b n| ≤ (C : ℝ) * b n := by
      intro n _
      rw [abs_mul, abs_of_nonneg (hb n)]
      have hle : |(g n : ℝ)| ≤ (C : ℝ) := by
        have hz : (|g n| : ℤ) ≤ (C : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast hg n
        rw [← Int.cast_abs]; exact_mod_cast hz
      exact mul_le_mul_of_nonneg_right hle (hb n)
    refine le_trans (Finset.sum_le_sum hbnd) ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hb n)
  have hgK1 : (1 : ℝ) ≤ |(g K : ℝ)| := by
    have hne : g K ≠ 0 := Finsupp.mem_support_iff.mp hKmem
    have hz : (1 : ℤ) ≤ |g K| := by rw [Int.abs_eq_natAbs]; exact_mod_cast Int.natAbs_pos.mpr hne
    rw [← Int.cast_abs]; exact_mod_cast hz
  have hbK : 0 ≤ b K := hb K
  rw [hsplit]
  have hrev := abs_sub_abs_le_abs_add ((g K : ℝ) * b K)
      (∑ n ∈ g.support.erase K, (g n : ℝ) * b n)
  have habsGK : |(g K : ℝ) * b K| = |(g K : ℝ)| * b K := by rw [abs_mul, abs_of_nonneg hbK]
  have hsum_le : ∑ n ∈ Finset.range K, b n ≤ b K / ((C:ℝ)+1) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith [hsiK]
  have hstep : b K / ((C : ℝ) + 1) ≤ |(g K : ℝ)| * b K
      - |∑ n ∈ g.support.erase K, (g n : ℝ) * b n| := by
    have h1 : (C : ℝ) * ∑ n ∈ Finset.range K, b n ≤ (C : ℝ) / ((C:ℝ)+1) * b K := by
      rw [div_mul_eq_mul_div, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hsum_le (by positivity)
    have h2 : b K ≤ |(g K : ℝ)| * b K := by
      calc b K = 1 * b K := (one_mul _).symm
        _ ≤ |(g K : ℝ)| * b K := mul_le_mul_of_nonneg_right hgK1 hbK
    have h3 : b K - (C : ℝ) / ((C:ℝ)+1) * b K = b K / ((C:ℝ)+1) := by field_simp; ring
    linarith [htail]
  linarith [hrev, hstep, habsGK]

/-- **Tail pairwise valuation gap.**  Two distinct `≤ D`-bounded multi-indices that agree below
`N₀` differ at some top index `K ≥ N₀`, and their valuations are separated by `b K/(D+1)` under a
tail-super-increasing profile — the superlacunar-compatible gap. -/
theorem finsupp_pair_valuation_gap_tail {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n) {D N₀ : ℕ}
    (hsi : ∀ k, N₀ ≤ k → ((D : ℝ) + 1) * (∑ n ∈ Finset.range k, b n) ≤ b k)
    {ν ν' : ℕ →₀ ℕ} (hν : ∀ n, ν n ≤ D) (hν' : ∀ n, ν' n ≤ D) (hne : ν ≠ ν')
    (hagree : ∀ n, n < N₀ → ν n = ν' n) :
    ∃ K : ℕ, N₀ ≤ K ∧ b K / ((D : ℝ) + 1)
      ≤ |ν.sum (fun n k => (k : ℝ) * b n) - ν'.sum (fun n k => (k : ℝ) * b n)| := by
  classical
  set g : ℕ →₀ ℤ := ν.mapRange (Nat.cast : ℕ → ℤ) Nat.cast_zero
    - ν'.mapRange (Nat.cast : ℕ → ℤ) Nat.cast_zero with hg
  have hgn : ∀ n, g n = (ν n : ℤ) - (ν' n : ℤ) := by
    intro n; rw [hg]; simp [Finsupp.sub_apply, Finsupp.mapRange_apply]
  have hgbound : ∀ n, (g n).natAbs ≤ D := by
    intro n; rw [hgn]; have h1 := hν n; have h2 := hν' n; omega
  have hg0 : g ≠ 0 := by
    intro h0; apply hne; ext n
    have := hgn n; rw [h0] at this; simp at this; omega
  have hne0 := Finsupp.support_nonempty_iff.mpr hg0
  set K := g.support.max' hne0 with hKdef
  have hKmem : K ∈ g.support := Finset.max'_mem _ _
  have hKge : N₀ ≤ K := by
    by_contra hlt
    push_neg at hlt
    rw [Finsupp.mem_support_iff, hgn] at hKmem
    apply hKmem
    rw [hagree K hlt]; ring
  have hval : ∑ n ∈ g.support, (g n : ℝ) * b n
      = ν.sum (fun n k => (k : ℝ) * b n) - ν'.sum (fun n k => (k : ℝ) * b n) := by
    rw [Finsupp.sum, Finsupp.sum]
    have hsupp : g.support ⊆ ν.support ∪ ν'.support := by
      intro n hn
      rw [Finsupp.mem_support_iff, hgn] at hn
      simp only [Finset.mem_union, Finsupp.mem_support_iff]
      by_contra hc; push_neg at hc; rw [hc.1, hc.2] at hn; simp at hn
    rw [Finset.sum_subset (Finset.subset_union_left (s₁ := ν.support) (s₂ := ν'.support))
      (fun n _ hn => by rw [Finsupp.notMem_support_iff.mp hn]; simp)]
    rw [Finset.sum_subset (Finset.subset_union_right (s₁ := ν.support) (s₂ := ν'.support))
      (fun n _ hn => by rw [Finsupp.notMem_support_iff.mp hn]; simp)]
    rw [Finset.sum_subset hsupp (fun n _ hn => by
      rw [Finsupp.notMem_support_iff.mp hn]; simp), ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _; rw [hgn]; push_cast; ring
  have hgap := valuation_gap_of_hsi_at_max hb hgbound hg0 (hsi K hKge)
  exact ⟨K, hKge, by rw [← hval]; exact hgap⟩

/-- Tail version of single-atom levels: distinct `≤ D`-bounded multi-indices agreeing below `N₀`
have distinct valuations under a tail-super-increasing profile. -/
theorem valuation_injOn_tail {b : ℕ → ℝ} (hbpos : ∀ n, 0 < b n) {D N₀ : ℕ}
    (hsi : ∀ k, N₀ ≤ k → ((D : ℝ) + 1) * (∑ n ∈ Finset.range k, b n) ≤ b k)
    {ν ν' : ℕ →₀ ℕ} (hν : ∀ n, ν n ≤ D) (hν' : ∀ n, ν' n ≤ D)
    (hagree : ∀ n, n < N₀ → ν n = ν' n)
    (hV : ν.sum (fun n k => (k : ℝ) * b n) = ν'.sum (fun n k => (k : ℝ) * b n)) :
    ν = ν' := by
  by_contra hne
  obtain ⟨K, _, hK⟩ :=
    finsupp_pair_valuation_gap_tail (fun n => (hbpos n).le) hsi hν hν' hne hagree
  rw [hV, sub_self, abs_zero] at hK
  have hpos : 0 < b K / ((D : ℝ) + 1) := by have := hbpos K; positivity
  linarith

/-- Tail uniform valuation gap: a finite family of `≤ D`-bounded multi-indices all agreeing
below `N₀` has a minimal-valuation member and a strictly positive gap below every other. -/
theorem exists_uniform_valuation_gap_tail {b : ℕ → ℝ} (hbpos : ∀ n, 0 < b n) {D N₀ : ℕ}
    (hsi : ∀ k, N₀ ≤ k → ((D : ℝ) + 1) * (∑ n ∈ Finset.range k, b n) ≤ b k)
    (K : Finset (ℕ →₀ ℕ)) (hKbound : ∀ ν ∈ K, ∀ n, ν n ≤ D) (hKne : K.Nonempty)
    (hKagree : ∀ ν ∈ K, ∀ ν' ∈ K, ∀ n, n < N₀ → ν n = ν' n) :
    ∃ ν₀ ∈ K, ∃ G : ℝ, 0 < G ∧ ∀ ν ∈ K.erase ν₀,
      ν₀.sum (fun n k => (k : ℝ) * b n) + G ≤ ν.sum (fun n k => (k : ℝ) * b n) := by
  classical
  obtain ⟨ν₀, hν₀K, hν₀min⟩ :=
    K.exists_min_image (fun ν => ν.sum (fun n k => (k : ℝ) * b n)) hKne
  refine ⟨ν₀, hν₀K, ?_⟩
  rcases (K.erase ν₀).eq_empty_or_nonempty with he | hne
  · exact ⟨1, one_pos, fun ν hν => absurd hν (he ▸ Finset.notMem_empty ν)⟩
  · obtain ⟨ν₁, hν₁, hν₁min⟩ := (K.erase ν₀).exists_min_image
      (fun ν => ν.sum (fun n k => (k : ℝ) * b n) - ν₀.sum (fun n k => (k : ℝ) * b n)) hne
    have hgap1 : 0 < ν₁.sum (fun n k => (k : ℝ) * b n) - ν₀.sum (fun n k => (k : ℝ) * b n) := by
      have hne' : ν₁ ≠ ν₀ := (Finset.mem_erase.mp hν₁).1
      have hν₁K := Finset.mem_of_mem_erase hν₁
      obtain ⟨Kidx, _, hK⟩ := finsupp_pair_valuation_gap_tail (fun n => (hbpos n).le) hsi
        (hKbound ν₁ hν₁K) (hKbound ν₀ hν₀K) hne' (hKagree ν₁ hν₁K ν₀ hν₀K)
      have hpos : 0 < b Kidx / ((D : ℝ) + 1) := by have := hbpos Kidx; positivity
      have hge := hν₀min ν₁ hν₁K
      rw [abs_of_nonneg (by linarith)] at hK
      linarith
    refine ⟨ν₁.sum (fun n k => (k : ℝ) * b n) - ν₀.sum (fun n k => (k : ℝ) * b n), hgap1,
      fun ν hν => ?_⟩
    have := hν₁min ν hν
    linarith

/-- **Support-restricted minimal-valuation domination.**  The valuation gap need only hold to the
*other nonzero-weight* atoms: an atom `i₀` with nonzero weight, minimal valuation among
nonzero-weight atoms with gap `G`, and total mass below `‖c i₀‖·exp G`, forces the weighted sum
nonzero.  Zero-weight atoms drop out of both the sum and the mass, so no global-minimum requirement
is needed — only that the distinguished atom beats every *competing* nonzero atom. -/
theorem weighted_sum_ne_zero_of_min_valuation_on_support {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (V : ι → ℝ) (a : ι → ℂ) (ha : ∀ i, ‖a i‖ = Real.exp (- V i)) (c : ι → ℂ) {i₀ : ι}
    (hi₀ : i₀ ∈ s) (hc : c i₀ ≠ 0) {G : ℝ}
    (hgap : ∀ i ∈ s, c i ≠ 0 → i ≠ i₀ → V i₀ + G ≤ V i)
    (hG : (∑ i ∈ s, ‖c i‖) < ‖c i₀‖ * Real.exp G) :
    ∑ i ∈ s, c i * a i ≠ 0 := by
  classical
  set s' := s.filter (fun i => c i ≠ 0) with hs'
  have hsum : ∑ i ∈ s, c i * a i = ∑ i ∈ s', c i * a i := by
    rw [hs']
    refine (Finset.sum_filter_of_ne fun i _ hci => ?_).symm
    intro h; exact hci (by rw [h, zero_mul])
  have hmass : ∑ i ∈ s', ‖c i‖ = ∑ i ∈ s, ‖c i‖ := by
    rw [hs']
    refine Finset.sum_filter_of_ne fun i _ hci => ?_
    intro h; rw [h, norm_zero] at hci; exact hci rfl
  have hi₀' : i₀ ∈ s' := Finset.mem_filter.mpr ⟨hi₀, hc⟩
  rw [hsum]
  refine weighted_sum_ne_zero_of_min_valuation_complex s' V a ha c hi₀' hc (G := G) ?_ ?_
  · intro i hi
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hi
    obtain ⟨his, hci⟩ := Finset.mem_filter.mp hmem
    exact hgap i his hci hne
  · rw [hmass]; exact hG

end GaloisForLFunctions
