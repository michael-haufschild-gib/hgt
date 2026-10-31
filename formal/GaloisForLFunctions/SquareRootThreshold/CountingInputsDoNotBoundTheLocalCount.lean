import Zeta23.Final

/-!
# Counting inputs do not bound the local count

The local count at scale `δ` asks for `#{ρ : |ρ − (½ + δ + it)| ≤ δ} ≤ C(δ log t + 1)`
(`LocalCountBound`).  Inputs that count zeros in windows of height `≥ 1` are blind to it.

**Theorem** (`exists_zeroConfig_rvm_not_localCountBound`).  There is a zero configuration `Z'` with
* the Riemann–von Mangoldt main term and the unit-window count (`RiemannVonMangoldt Z'`);
* exactly the critical zeros of `ζ` with their multiplicities: `N₀(Z') = N₀(ζ)` on every window;
* the window counts of `ζ` up to `4 log(|T₂| + 3)`:
  `N_ζ(T₁, T₂) ≤ N_{Z'}(T₁, T₂) ≤ N_ζ(T₁, T₂) + 4 log(|T₂| + 3)`;
* the zero-counting form of Lindelöf whenever `ζ` has it (`LindelofCount`);
* no constant `C` with `LocalCountBound Z' C`, and no `M` bounding the off-line multiplicity of the
  windows `(T − 1, T + 1]` (`OffLineLocallyBounded`, the input of the lag family).

`Z'` superposes (`ZeroConfig.superpose`) on the zeros of `ζ` the clusters `½ ± 1/(k+3) + i exp(eᵏ)`
of
multiplicity `⌊log γ⌋ = ⌊eᵏ⌋` (`clusterConfig`).  The heights grow doubly exponentially, so the
clusters below `T` carry `Σ_{eᵏ ≤ log T} 2⌊eᵏ⌋ ≤ 4 log T` zeros (`clusterConfig_N_le`).  Hence the
Riemann–von Mangoldt remainder, the unit-window count, the critical proportion, every near-line
density with a `log T` slack, and the Lindelöf count (finitely many clusters above each `σ > ½`)
survive; but at depth `δ = 1/(k+3)` the disc about `½ + δ + i exp(eᵏ)`
holds `⌊eᵏ⌋` zeros against `C(eᵏ/(k+3) + 1)` (`not_localCountBound_superpose`).

**What counting does give** (`volume_localCount_gt_le`, `eventually_volume_localCount_gt_le`).  For
any
configuration with Riemann–von Mangoldt, the heights `t ∈ [T, 2T]` violating the local count with
constant `C` have measure `≤ T/(πC) + K`: each zero lies in the disc about `½ + δ + it` for `t` in
an
interval of length `≤ 2δ`, and Markov's inequality divides `2δ N(T − 1, 2T + 1)` by `Cδ log T`.  So
counting gives the local count in density, never pointwise.
-/

open Complex Set Zeta23

namespace RHTower.LocalCountFalsifier

noncomputable section

open Classical

/-! ## Superposition of zero configurations -/

/-- The superposition of two zero configurations: union of carriers, multiplicities added. -/
def superpose (Z₁ Z₂ : ZeroConfig) : ZeroConfig where
  carrier := Z₁.carrier ∪ Z₂.carrier
  mult := fun ρ => (if ρ ∈ Z₁.carrier then Z₁.mult ρ else 0) +
    (if ρ ∈ Z₂.carrier then Z₂.mult ρ else 0)
  one_le_mult := by
    rintro ρ (h | h)
    · have := Z₁.one_le_mult ρ h; rw [if_pos h]; omega
    · have := Z₂.one_le_mult ρ h; rw [if_pos h]; omega
  strip := by
    rintro ρ (h | h)
    · exact Z₁.strip ρ h
    · exact Z₂.strip ρ h
  reflect_mem := by
    rintro ρ (h | h)
    · exact Or.inl (Z₁.reflect_mem ρ h)
    · exact Or.inr (Z₂.reflect_mem ρ h)
  mult_reflect := by
    intro ρ _
    have hrr : reflect (reflect ρ) = ρ := by simp [reflect]
    have key : ∀ Z : ZeroConfig, (if reflect ρ ∈ Z.carrier then Z.mult (reflect ρ) else 0)
        = (if ρ ∈ Z.carrier then Z.mult ρ else 0) := by
      intro Z
      by_cases h : ρ ∈ Z.carrier
      · rw [if_pos (Z.reflect_mem ρ h), if_pos h, Z.mult_reflect ρ h]
      · have h' : reflect ρ ∉ Z.carrier := fun h' => h (hrr ▸ Z.reflect_mem _ h')
        rw [if_neg h', if_neg h]
    rw [key Z₁, key Z₂]
  finite_window := fun T₁ T₂ => by
    refine ((Z₁.finite_window T₁ T₂).union (Z₂.finite_window T₁ T₂)).subset ?_
    rintro ρ ⟨h1 | h1, h2⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩

/-- Multiplicity sums are additive under superposition, on any set with finite traces. -/
theorem finsum_superpose (Z₁ Z₂ : ZeroConfig) {P : Set ℂ} (h₁ : (Z₁.carrier ∩ P).Finite)
    (h₂ : (Z₂.carrier ∩ P).Finite) :
    ∑ᶠ ρ ∈ (superpose Z₁ Z₂).carrier ∩ P, (superpose Z₁ Z₂).mult ρ
      = ∑ᶠ ρ ∈ Z₁.carrier ∩ P, Z₁.mult ρ + ∑ᶠ ρ ∈ Z₂.carrier ∩ P, Z₂.mult ρ := by
  have hU : (superpose Z₁ Z₂).carrier ∩ P = Z₁.carrier ∩ P ∪ Z₂.carrier ∩ P :=
    Set.union_inter_distrib_right _ _ _
  rw [hU]
  change ∑ᶠ ρ ∈ Z₁.carrier ∩ P ∪ Z₂.carrier ∩ P, ((if ρ ∈ Z₁.carrier then Z₁.mult ρ else 0) +
    (if ρ ∈ Z₂.carrier then Z₂.mult ρ else 0)) = _
  rw [finsum_mem_add_distrib (h₁.union h₂)]
  have e₁ : ∑ᶠ ρ ∈ Z₁.carrier ∩ P ∪ Z₂.carrier ∩ P, (if ρ ∈ Z₁.carrier then Z₁.mult ρ else 0)
      = ∑ᶠ ρ ∈ Z₁.carrier ∩ P, Z₁.mult ρ := by
    have h0 : ∑ᶠ ρ ∈ SDiff.sdiff (Z₂.carrier ∩ P) (Z₁.carrier ∩ P),
        (if ρ ∈ Z₁.carrier then Z₁.mult ρ else 0) = 0 :=
      finsum_mem_of_eqOn_zero fun ρ hρ => by
        rw [if_neg fun hc => hρ.2 ⟨hc, hρ.1.2⟩, Pi.zero_apply]
    rw [← Set.union_sdiff_self, finsum_mem_union Set.disjoint_sdiff_right h₁ h₂.sdiff, h0,
      add_zero]
    exact finsum_mem_congr rfl fun ρ hρ => if_pos hρ.1
  have e₂ : ∑ᶠ ρ ∈ Z₁.carrier ∩ P ∪ Z₂.carrier ∩ P, (if ρ ∈ Z₂.carrier then Z₂.mult ρ else 0)
      = ∑ᶠ ρ ∈ Z₂.carrier ∩ P, Z₂.mult ρ := by
    have h0 : ∑ᶠ ρ ∈ SDiff.sdiff (Z₁.carrier ∩ P) (Z₂.carrier ∩ P),
        (if ρ ∈ Z₂.carrier then Z₂.mult ρ else 0) = 0 :=
      finsum_mem_of_eqOn_zero fun ρ hρ => by
        rw [if_neg fun hc => hρ.2 ⟨hc, hρ.1.2⟩, Pi.zero_apply]
    rw [Set.union_comm, ← Set.union_sdiff_self,
      finsum_mem_union Set.disjoint_sdiff_right h₂ h₁.sdiff, h0, add_zero]
    exact finsum_mem_congr rfl fun ρ hρ => if_pos hρ.1
  rw [e₁, e₂]

theorem N_superpose (Z₁ Z₂ : ZeroConfig) (T₁ T₂ : ℝ) :
    (superpose Z₁ Z₂).N T₁ T₂ = Z₁.N T₁ T₂ + Z₂.N T₁ T₂ :=
  finsum_superpose Z₁ Z₂ (Z₁.finite_window T₁ T₂) (Z₂.finite_window T₁ T₂)

theorem N0_superpose (Z₁ Z₂ : ZeroConfig) (T₁ T₂ : ℝ) :
    (superpose Z₁ Z₂).N0 T₁ T₂ = Z₁.N0 T₁ T₂ + Z₂.N0 T₁ T₂ := by
  simp only [ZeroConfig.N0, ZeroConfig.window, Set.inter_assoc]
  exact finsum_superpose Z₁ Z₂ ((Z₁.finite_window T₁ T₂).subset (by
      rw [← Set.inter_assoc]; exact Set.inter_subset_left))
    ((Z₂.finite_window T₁ T₂).subset (by rw [← Set.inter_assoc]; exact Set.inter_subset_left))

/-! ## The cluster configuration -/

/-- `½ + s/(k+3) + i exp(eᵏ)`. -/
def clusterPoint (s : ℝ) (k : ℕ) : ℂ := ⟨1 / 2 + s / ((k : ℝ) + 3), Real.exp (Real.exp k)⟩

theorem clusterPoint_re (s : ℝ) (k : ℕ) : (clusterPoint s k).re = 1 / 2 + s / ((k : ℝ) + 3) := rfl

theorem clusterPoint_im (s : ℝ) (k : ℕ) : (clusterPoint s k).im = Real.exp (Real.exp k) := rfl

theorem log_clusterPoint_im (s : ℝ) (k : ℕ) : Real.log (clusterPoint s k).im = Real.exp k := by
  rw [clusterPoint_im, Real.log_exp]

theorem reflect_clusterPoint (s : ℝ) (k : ℕ) :
    reflect (clusterPoint s k) = clusterPoint (-s) k := by
  apply Complex.ext <;> simp [reflect, clusterPoint]
  ring

theorem le_exp_exp (k : ℕ) : (k : ℝ) + 2 ≤ Real.exp (Real.exp k) := by
  have h1 := Real.add_one_le_exp (k : ℝ)
  have h2 := Real.add_one_le_exp (Real.exp k)
  linarith

/-- **The clusters.**  At each height `exp(eᵏ)` the pair `½ ± 1/(k+3)`, each of multiplicity
`⌊log γ⌋ = ⌊eᵏ⌋`. -/
def clusterConfig : ZeroConfig where
  carrier := Set.range (clusterPoint 1) ∪ Set.range (clusterPoint (-1))
  mult := fun ρ => ⌊Real.log ρ.im⌋₊
  one_le_mult := by
    rintro _ (⟨k, rfl⟩ | ⟨k, rfl⟩) <;>
    · rw [log_clusterPoint_im]
      exact Nat.le_floor (by rw [Nat.cast_one]; exact Real.one_le_exp (Nat.cast_nonneg k))
  strip := by
    have h3 : ∀ k : ℕ, 1 / ((k : ℝ) + 3) ≤ 1 / 2 := fun k => by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have h0 : ∀ k : ℕ, 0 ≤ 1 / ((k : ℝ) + 3) := fun k => by positivity
    rintro _ (⟨k, rfl⟩ | ⟨k, rfl⟩) <;> rw [clusterPoint_re]
    · constructor <;> linarith [h3 k, h0 k]
    · rw [neg_div]; constructor <;> linarith [h3 k, h0 k]
  reflect_mem := by
    rintro _ (⟨k, rfl⟩ | ⟨k, rfl⟩)
    · exact Or.inr ⟨k, by rw [reflect_clusterPoint]⟩
    · exact Or.inl ⟨k, by rw [reflect_clusterPoint, neg_neg]⟩
  mult_reflect := fun ρ _ => by simp [reflect]
  finite_window := by
    intro T₁ T₂
    have hF : (Finset.range ⌈T₂⌉₊ : Set ℕ).Finite := Finset.finite_toSet _
    refine ((hF.image (clusterPoint 1)).union (hF.image (clusterPoint (-1)))).subset ?_
    have hk : ∀ k : ℕ, Real.exp (Real.exp k) ≤ T₂ → k ∈ (Finset.range ⌈T₂⌉₊ : Set ℕ) := by
      intro k hk
      simp only [Finset.coe_range, Set.mem_Iio]
      exact Nat.lt_ceil.mpr (by linarith [le_exp_exp k])
    rintro _ ⟨⟨k, rfl⟩ | ⟨k, rfl⟩, -, h2⟩
    · exact Or.inl ⟨k, hk k h2, rfl⟩
    · exact Or.inr ⟨k, hk k h2, rfl⟩

theorem clusterConfig_mult (s : ℝ) (k : ℕ) :
    clusterConfig.mult (clusterPoint s k) = ⌊Real.exp k⌋₊ := by
  show ⌊Real.log (clusterPoint s k).im⌋₊ = _
  rw [log_clusterPoint_im]

/-- `Σ_{k<n} eᵏ ≤ 2 e^{n−1}`, through `e/(e − 1) ≤ 2`. -/
theorem sum_range_exp_le (n : ℕ) :
    ∑ k ∈ Finset.range n, Real.exp k ≤ 2 * Real.exp n / Real.exp 1 := by
  have he := Real.exp_one_gt_d9
  have hgeo := geom_sum_eq (x := Real.exp 1) (by linarith) n
  simp only [Real.exp_one_pow] at hgeo
  rw [hgeo, div_le_div_iff₀ (by linarith) (by linarith)]
  have hn : 1 ≤ Real.exp n := Real.one_le_exp (Nat.cast_nonneg n)
  nlinarith

/-- **The clusters are sparse.**  `N_clusters(T₁, T₂) ≤ 4 log(|T₂| + 3)`. -/
theorem clusterConfig_N_le (T₁ T₂ : ℝ) :
    (clusterConfig.N T₁ T₂ : ℝ) ≤ 4 * Real.log (|T₂| + 3) := by
  have hlog0 : 0 ≤ Real.log (|T₂| + 3) := Real.log_nonneg (by linarith [abs_nonneg T₂])
  rcases (clusterConfig.window T₁ T₂).eq_empty_or_nonempty with hE | ⟨ρ₀, hρ₀⟩
  · have : clusterConfig.N T₁ T₂ = 0 := by
      simp only [ZeroConfig.N, hE, finsum_mem_empty]
    rw [this, Nat.cast_zero]; positivity
  -- some cluster height lies below `T₂`, so `log T₂ ≥ 1`
  have hT₂ : Real.exp 1 ≤ T₂ := by
    obtain ⟨⟨k, rfl⟩ | ⟨k, rfl⟩, -, h2⟩ := hρ₀ <;>
    · rw [clusterPoint_im] at h2
      exact le_trans (Real.exp_le_exp.mpr (Real.one_le_exp (Nat.cast_nonneg k))) h2
  have hT₂0 : 0 < T₂ := lt_of_lt_of_le (Real.exp_pos 1) hT₂
  have hL1 : 1 ≤ Real.log T₂ := by rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hT₂
  set n : ℕ := ⌊Real.log (Real.log T₂)⌋₊ + 1 with hn
  set S : Finset ℂ := (Finset.range n ×ˢ ({1, -1} : Finset ℝ)).image
    (fun p => clusterPoint p.2 p.1) with hS
  have hfin := clusterConfig.finite_window T₁ T₂
  have hsub : hfin.toFinset ⊆ S := by
    intro ρ hρ
    rw [Set.Finite.mem_toFinset] at hρ
    have hk : ∀ k : ℕ, Real.exp (Real.exp k) ≤ T₂ → k ∈ Finset.range n := by
      intro k hk
      have h1 : Real.exp k ≤ Real.log T₂ := by
        rw [← Real.log_exp (Real.exp k)]; exact Real.log_le_log (Real.exp_pos _) hk
      have h2 : (k : ℝ) ≤ Real.log (Real.log T₂) := by
        rw [← Real.log_exp k]; exact Real.log_le_log (Real.exp_pos _) h1
      rw [Finset.mem_range, hn]
      have := Nat.le_floor h2
      omega
    obtain ⟨⟨k, rfl⟩ | ⟨k, rfl⟩, -, h2⟩ := hρ
    · exact Finset.mem_image.mpr ⟨(k, 1), Finset.mem_product.mpr ⟨hk k h2, by simp⟩, rfl⟩
    · exact Finset.mem_image.mpr ⟨(k, -1), Finset.mem_product.mpr ⟨hk k h2, by simp⟩, rfl⟩
  have hN : clusterConfig.N T₁ T₂ ≤ ∑ k ∈ Finset.range n, 2 * ⌊Real.exp k⌋₊ := by
    calc clusterConfig.N T₁ T₂ = ∑ ρ ∈ hfin.toFinset, clusterConfig.mult ρ :=
          finsum_mem_eq_finite_toFinset_sum _ hfin
      _ ≤ ∑ ρ ∈ S, clusterConfig.mult ρ := Finset.sum_le_sum_of_subset hsub
      _ ≤ ∑ p ∈ Finset.range n ×ˢ ({1, -1} : Finset ℝ), clusterConfig.mult (clusterPoint p.2 p.1) :=
          Finset.sum_image_le_of_nonneg fun _ _ => Nat.zero_le _
      _ = ∑ k ∈ Finset.range n, 2 * ⌊Real.exp k⌋₊ := by
          rw [Finset.sum_product]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_pair (by norm_num), clusterConfig_mult, clusterConfig_mult]
          ring
  have hcast : ((∑ k ∈ Finset.range n, 2 * ⌊Real.exp k⌋₊ : ℕ) : ℝ)
      ≤ 2 * ∑ k ∈ Finset.range n, Real.exp k := by
    push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => by
      have := Nat.floor_le (Real.exp_pos (k : ℝ)).le
      linarith
  -- `e^n ≤ e log T₂`
  have hexpn : Real.exp n ≤ Real.exp 1 * Real.log T₂ := by
    have hfl : (⌊Real.log (Real.log T₂)⌋₊ : ℝ) ≤ Real.log (Real.log T₂) :=
      Nat.floor_le (Real.log_nonneg hL1)
    have : Real.exp (⌊Real.log (Real.log T₂)⌋₊ : ℝ) ≤ Real.log T₂ := by
      calc _ ≤ Real.exp (Real.log (Real.log T₂)) := Real.exp_le_exp.mpr hfl
        _ = Real.log T₂ := Real.exp_log (by linarith)
    rw [hn, Nat.cast_add, Nat.cast_one, Real.exp_add, mul_comm]
    exact mul_le_mul_of_nonneg_left this (Real.exp_pos 1).le
  have hlogT : Real.log T₂ ≤ Real.log (|T₂| + 3) :=
    Real.log_le_log hT₂0 (by rw [abs_of_pos hT₂0]; linarith)
  have he := Real.exp_pos 1
  calc (clusterConfig.N T₁ T₂ : ℝ) ≤ ((∑ k ∈ Finset.range n, 2 * ⌊Real.exp k⌋₊ : ℕ) : ℝ) := by
        exact_mod_cast hN
    _ ≤ 2 * (2 * Real.exp n / Real.exp 1) :=
        hcast.trans (mul_le_mul_of_nonneg_left (sum_range_exp_le n) (by norm_num))
    _ ≤ 4 * Real.log T₂ := by
        rw [mul_div_assoc', div_le_iff₀ he]
        nlinarith
    _ ≤ 4 * Real.log (|T₂| + 3) := by linarith

theorem clusterConfig_N0 (T₁ T₂ : ℝ) : clusterConfig.N0 T₁ T₂ = 0 := by
  refine finsum_mem_of_eqOn_zero fun ρ hρ => ?_
  exfalso
  obtain ⟨⟨⟨k, rfl⟩ | ⟨k, rfl⟩, -⟩, hon⟩ := hρ <;>
  · change (clusterPoint _ k).re = 1 / 2 at hon
    rw [clusterPoint_re] at hon
    have : (0 : ℝ) < (k : ℝ) + 3 := by positivity
    have h := hon
    field_simp at h
    linarith

/-! ## Riemann–von Mangoldt survives the clusters -/

theorem riemannVonMangoldt_superpose {Z : ZeroConfig} (h : RiemannVonMangoldt Z) :
    RiemannVonMangoldt (superpose Z clusterConfig) where
  main := by
    obtain ⟨C, T₀, hC⟩ := h.main
    refine ⟨C + 8, max T₀ 3, fun T hT => ?_⟩
    have hT₀ : T₀ ≤ T := le_trans (le_max_left _ _) hT
    have hT3 : 3 ≤ T := le_trans (le_max_right _ _) hT
    have hlog : Real.log (|2 * T| + 3) ≤ 2 * Real.log T := by
      rw [abs_of_pos (by linarith), ← Real.log_rpow (by linarith)]
      refine Real.log_le_log (by linarith) ?_
      rw [show (T : ℝ) ^ (2 : ℝ) = T ^ 2 by norm_cast]
      nlinarith
    have hc := clusterConfig_N_le T (2 * T)
    have hc0 : (0 : ℝ) ≤ clusterConfig.N T (2 * T) := Nat.cast_nonneg _
    rw [N_superpose, Nat.cast_add]
    have h1 := hC T hT₀
    have hL0 : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
    rw [abs_le] at h1 ⊢
    constructor <;> nlinarith
  local_count := by
    obtain ⟨A₀, hA₀, hloc⟩ := h.local_count
    refine ⟨A₀ + 8, by linarith, fun t => ?_⟩
    have hlog : Real.log (|t + 1| + 3) ≤ 2 * Real.log (|t| + 3) := by
      rw [← Real.log_rpow (by positivity)]
      refine Real.log_le_log (by positivity) ?_
      rw [show (|t| + 3 : ℝ) ^ (2 : ℝ) = (|t| + 3) ^ 2 by norm_cast]
      have := abs_add_le t 1
      rw [abs_one] at this
      nlinarith [abs_nonneg t]
    have hc := clusterConfig_N_le t (t + 1)
    have hL0 : 0 ≤ Real.log (|t| + 3) := Real.log_nonneg (by linarith [abs_nonneg t])
    rw [N_superpose, Nat.cast_add]
    nlinarith [hloc t]

/-! ## The local count fails -/

/-- Zeros with multiplicity in the closed disc of radius `r` about `c`. -/
def discCount (Z : ZeroConfig) (c : ℂ) (r : ℝ) : ℕ :=
  ∑ᶠ ρ ∈ Z.carrier ∩ Metric.closedBall c r, Z.mult ρ

/-- The local count at scale `δ`: `#{ρ : |ρ − (½ + δ + it)| ≤ δ} ≤ C(δ log t + 1)` for
`0 < δ ≤ ½`, `t ≥ 3`. -/
def LocalCountBound (Z : ZeroConfig) (C : ℝ) : Prop :=
  ∀ δ t : ℝ, 0 < δ → δ ≤ 1 / 2 → 3 ≤ t →
    (discCount Z (((1 / 2 + δ : ℝ) : ℂ) + (t : ℂ) * I) δ : ℝ) ≤ C * (δ * Real.log t + 1)

/-- A point of the carrier contributes its multiplicity to the disc count. -/
theorem mult_le_discCount (Z : ZeroConfig) {c ρ : ℂ} {r : ℝ} (hr : r ≤ 1 / 2) (hρ : ρ ∈ Z.carrier)
    (hρc : ρ ∈ Metric.closedBall c r) : Z.mult ρ ≤ discCount Z c r := by
  have hfin : (Z.carrier ∩ Metric.closedBall c r).Finite := by
    refine (Z.finite_window (c.im - 1) (c.im + 1)).subset fun z hz => ⟨hz.1, ?_⟩
    have hd : ‖z - c‖ ≤ r := by rw [← Complex.dist_eq]; exact Metric.mem_closedBall.mp hz.2
    have h := (Complex.abs_im_le_norm (z - c)).trans hd
    rw [Complex.sub_im] at h
    have := abs_le.mp (h.trans hr)
    exact ⟨by linarith, by linarith⟩
  unfold discCount
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (hfin.mem_toFinset.mpr ⟨hρ, hρc⟩)

/-- **The clusters violate every local count.** -/
theorem not_localCountBound_superpose (Z : ZeroConfig) (C : ℝ) :
    ¬ LocalCountBound (superpose Z clusterConfig) C := by
  intro hC
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = ⌈2 * (|C| + 2)⌉₊ := ⟨_, rfl⟩
  have hkC : 2 * (|C| + 2) ≤ (k : ℝ) := by rw [hk]; exact Nat.le_ceil _
  have hk0 : (0 : ℝ) < (k : ℝ) + 3 := by positivity
  set δ : ℝ := 1 / ((k : ℝ) + 3) with hδ
  set t : ℝ := Real.exp (Real.exp k) with ht
  have hδ0 : 0 < δ := by positivity
  have hδ2 : δ ≤ 1 / 2 := by
    rw [hδ, div_le_div_iff₀ hk0 (by norm_num)]; linarith [abs_nonneg C]
  have ht3 : 3 ≤ t := by have := le_exp_exp k; have : (1 : ℝ) ≤ k := by linarith [abs_nonneg C]
                         linarith
  have hcentre : ((1 / 2 + δ : ℝ) : ℂ) + (t : ℂ) * I = clusterPoint 1 k := by
    apply Complex.ext
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, clusterPoint_re]
      rw [hδ]; ring
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_re, Complex.I_im, clusterPoint_im]
      rw [ht]; ring
  have hmem : clusterPoint 1 k ∈ (superpose Z clusterConfig).carrier :=
    Or.inr (Or.inl ⟨k, rfl⟩)
  have hlow : ⌊Real.exp k⌋₊ ≤ discCount (superpose Z clusterConfig)
      (((1 / 2 + δ : ℝ) : ℂ) + (t : ℂ) * I) δ := by
    rw [hcentre]
    refine le_trans ?_ (mult_le_discCount _ hδ2 hmem (Metric.mem_closedBall_self hδ0.le))
    have hc : clusterPoint 1 k ∈ clusterConfig.carrier := Or.inl ⟨k, rfl⟩
    show ⌊Real.exp k⌋₊ ≤ (if clusterPoint 1 k ∈ Z.carrier then Z.mult (clusterPoint 1 k) else 0) +
      (if clusterPoint 1 k ∈ clusterConfig.carrier then clusterConfig.mult (clusterPoint 1 k)
        else 0)
    rw [if_pos hc, clusterConfig_mult]
    omega
  have hbound := hC δ t hδ0 hδ2 ht3
  have hfl : Real.exp k - 1 < (⌊Real.exp k⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one (Real.exp k); linarith
  have hlowR : (⌊Real.exp k⌋₊ : ℝ) ≤ (discCount (superpose Z clusterConfig)
      (((1 / 2 + δ : ℝ) : ℂ) + (t : ℂ) * I) δ : ℝ) := by exact_mod_cast hlow
  have hlogt : Real.log t = Real.exp k := by rw [ht, Real.log_exp]
  rw [hlogt] at hbound
  -- `C(eᵏ/(k+3) + 1) ≤ eᵏ/2 + |C| < eᵏ − 1`
  have hek : (k : ℝ) + 1 ≤ Real.exp k := Real.add_one_le_exp _
  have hCδ : |C| * δ ≤ 1 / 2 := by
    rw [hδ, mul_one_div, div_le_div_iff₀ hk0 (by norm_num)]; linarith [abs_nonneg C]
  have hpos : 0 ≤ δ * Real.exp k + 1 := by positivity
  have hCle : C * (δ * Real.exp k + 1) ≤ |C| * (δ * Real.exp k + 1) :=
    mul_le_mul_of_nonneg_right (le_abs_self C) hpos
  have hexp0 := Real.exp_pos (k : ℝ)
  nlinarith [mul_le_mul_of_nonneg_right hCδ hexp0.le, abs_nonneg C]

/-- Off-line multiplicity in every window `(T − 1, T + 1]` is at most `M`: the input of the lag
family. -/
def OffLineLocallyBounded (Z : ZeroConfig) (M : ℕ) : Prop :=
  ∀ T : ℝ, ∑ᶠ ρ ∈ Z.window (T - 1) (T + 1) ∩ {ρ | ρ.re ≠ 1 / 2}, Z.mult ρ ≤ M

/-- **The clusters violate every off-line local bound.** -/
theorem not_offLineLocallyBounded_superpose (Z : ZeroConfig) (M : ℕ) :
    ¬ OffLineLocallyBounded (superpose Z clusterConfig) M := by
  intro h
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = M + 1 := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = Real.exp (Real.exp k) := ⟨_, rfl⟩
  have hfin : ((superpose Z clusterConfig).window (T - 1) (T + 1) ∩ {ρ | ρ.re ≠ 1 / 2}).Finite :=
    ((superpose Z clusterConfig).finite_window (T - 1) (T + 1)).subset Set.inter_subset_left
  have hmem : clusterPoint 1 k ∈
      (superpose Z clusterConfig).window (T - 1) (T + 1) ∩ {ρ | ρ.re ≠ 1 / 2} := by
    refine ⟨⟨Or.inr (Or.inl ⟨k, rfl⟩), ?_, ?_⟩, ?_⟩
    · rw [clusterPoint_im, ← hT]; linarith
    · rw [clusterPoint_im, ← hT]; linarith
    · show (clusterPoint 1 k).re ≠ 1 / 2
      rw [clusterPoint_re]
      have : 0 < 1 / ((k : ℝ) + 3) := by positivity
      linarith
  have h1 := h T
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at h1
  have h2 := Finset.single_le_sum (f := (superpose Z clusterConfig).mult)
    (fun _ _ => Nat.zero_le _) (hfin.mem_toFinset.mpr hmem)
  have h3 : ⌊Real.exp k⌋₊ ≤ (superpose Z clusterConfig).mult (clusterPoint 1 k) := by
    show ⌊Real.exp k⌋₊ ≤ (if clusterPoint 1 k ∈ Z.carrier then Z.mult (clusterPoint 1 k) else 0) +
      (if clusterPoint 1 k ∈ clusterConfig.carrier then clusterConfig.mult (clusterPoint 1 k)
        else 0)
    have hc : clusterPoint 1 k ∈ clusterConfig.carrier := Or.inl ⟨k, rfl⟩
    rw [if_pos hc, clusterConfig_mult]
    omega
  have h4 : M + 1 ≤ ⌊Real.exp k⌋₊ := by
    refine Nat.le_floor ?_
    have := Real.add_one_le_exp (k : ℝ)
    rw [hk] at this ⊢
    push_cast at this ⊢
    linarith
  omega

/-- The zero-counting form of the Lindelöf hypothesis: for every `σ > ½` the zeros with
`Re ρ ≥ σ` in `(T, T + 1]` are `o(log T)`. -/
def LindelofCount (Z : ZeroConfig) : Prop :=
  ∀ σ : ℝ, 1 / 2 < σ → ∀ ε : ℝ, 0 < ε → ∀ᶠ T in Filter.atTop,
    (((∑ᶠ ρ ∈ Z.carrier ∩ ({ρ | T < ρ.im ∧ ρ.im ≤ T + 1} ∩ {ρ | σ ≤ ρ.re}), Z.mult ρ) : ℕ) : ℝ)
      ≤ ε * Real.log T

/-- **The clusters keep the Lindelöf count**: above any `σ > ½` only finitely many clusters lie. -/
theorem lindelofCount_superpose {Z : ZeroConfig} (h : LindelofCount Z) :
    LindelofCount (superpose Z clusterConfig) := by
  intro σ hσ ε hε
  obtain ⟨K, hK⟩ := exists_nat_gt (1 / (σ - 1 / 2))
  filter_upwards [h σ hσ ε hε, Filter.eventually_ge_atTop (Real.exp (Real.exp K))] with T hT hTK
  have hP : ∀ Z' : ZeroConfig,
      (Z'.carrier ∩ ({ρ | T < ρ.im ∧ ρ.im ≤ T + 1} ∩ {ρ | σ ≤ ρ.re})).Finite :=
    fun Z' => (Z'.finite_window T (T + 1)).subset fun ρ hρ => ⟨hρ.1, hρ.2.1⟩
  rw [finsum_superpose Z clusterConfig (hP Z) (hP clusterConfig)]
  have h0 : ∑ᶠ ρ ∈ clusterConfig.carrier ∩ ({ρ | T < ρ.im ∧ ρ.im ≤ T + 1} ∩ {ρ | σ ≤ ρ.re}),
      clusterConfig.mult ρ = 0 := by
    refine finsum_mem_of_eqOn_zero fun ρ hρ => ?_
    exfalso
    obtain ⟨hρC, ⟨hlo, -⟩, hre⟩ := hρ
    have hσ0 : 0 < σ - 1 / 2 := by linarith
    -- a cluster point above `σ` has `k + 3 ≤ 1/(σ − ½) < K`, hence height `≤ exp(e^K) ≤ T`
    have hsmall : ∀ k : ℕ, σ ≤ (clusterPoint 1 k).re → k < K := by
      intro k hk
      rw [clusterPoint_re] at hk
      have h1 : σ - 1 / 2 ≤ 1 / ((k : ℝ) + 3) := by linarith
      have h2 : ((k : ℝ) + 3) * (σ - 1 / 2) ≤ 1 := by
        rw [le_div_iff₀ (by positivity)] at h1; linarith
      have h3 : (k : ℝ) + 3 ≤ 1 / (σ - 1 / 2) := by rw [le_div_iff₀ hσ0]; linarith
      exact_mod_cast (by linarith : (k : ℝ) < K)
    rcases hρC with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · have hk := hsmall k hre
      have hlo' : T < (clusterPoint 1 k).im := hlo
      rw [clusterPoint_im] at hlo'
      have : Real.exp (Real.exp k) ≤ Real.exp (Real.exp K) :=
        Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by exact_mod_cast hk.le))
      linarith
    · have hre' : σ ≤ (clusterPoint (-1) k).re := hre
      rw [clusterPoint_re, neg_div] at hre'
      have : 0 < 1 / ((k : ℝ) + 3) := by positivity
      linarith
  rw [h0, add_zero]
  exact hT

/-! ## The falsifier -/

/-- **Counting inputs do not bound the local count.**  The zeros of `ζ` with the sparse clusters
satisfy Riemann–von Mangoldt, keep the critical zeros of `ζ`, change every window count by at most
`4 log(|T₂| + 3)`, and violate the local count at scale `δ` and the off-line local bound for every
constant. -/
theorem exists_zeroConfig_rvm_not_localCountBound :
    ∃ Z' : ZeroConfig, RiemannVonMangoldt Z' ∧
      (∀ T₁ T₂ : ℝ, Z'.N0 T₁ T₂ = zetaZeroConfig.N0 T₁ T₂) ∧
      (∀ T₁ T₂ : ℝ, zetaZeroConfig.N T₁ T₂ ≤ Z'.N T₁ T₂ ∧
        (Z'.N T₁ T₂ : ℝ) ≤ zetaZeroConfig.N T₁ T₂ + 4 * Real.log (|T₂| + 3)) ∧
      (LindelofCount zetaZeroConfig → LindelofCount Z') ∧
      (∀ C : ℝ, ¬ LocalCountBound Z' C) ∧ ∀ M : ℕ, ¬ OffLineLocallyBounded Z' M := by
  refine ⟨superpose zetaZeroConfig clusterConfig,
    riemannVonMangoldt_superpose riemannVonMangoldt_zeta, fun T₁ T₂ => ?_, fun T₁ T₂ => ?_,
    lindelofCount_superpose, not_localCountBound_superpose zetaZeroConfig,
    not_offLineLocallyBounded_superpose zetaZeroConfig⟩
  · rw [N0_superpose, clusterConfig_N0, add_zero]
  · rw [N_superpose]
    refine ⟨Nat.le_add_right _ _, ?_⟩
    rw [Nat.cast_add]
    linarith [clusterConfig_N_le T₁ T₂]

/-! ## What counting does give: the local count in measure -/

/-- On `t ∈ [T, 2T]` the disc count is a finite sum over the zeros of the window `(T − 1, 2T + 1]`.
-/
theorem discCount_eq_sum (Z : ZeroConfig) {δ T t : ℝ} (hδ : δ ≤ 1 / 2) (ht : t ∈ Icc T (2 * T)) :
    discCount Z (((1 / 2 + δ : ℝ) : ℂ) + (t : ℂ) * I) δ =
      ∑ ρ ∈ (Z.finite_window (T - 1) (2 * T + 1)).toFinset,
        if ρ ∈ Metric.closedBall (((1 / 2 + δ : ℝ) : ℂ) + (t : ℂ) * I) δ then Z.mult ρ else 0 := by
  set c : ℂ := ((1 / 2 + δ : ℝ) : ℂ) + (t : ℂ) * I with hc
  have hsub : Z.carrier ∩ Metric.closedBall c δ ⊆
      Z.carrier ∩ {ρ | T - 1 < ρ.im ∧ ρ.im ≤ 2 * T + 1} := by
    intro z hz
    refine ⟨hz.1, ?_⟩
    have hd : ‖z - c‖ ≤ δ := by rw [← Complex.dist_eq]; exact Metric.mem_closedBall.mp hz.2
    have h := (Complex.abs_im_le_norm (z - c)).trans hd
    have hci : c.im = t := by simp [hc]
    rw [Complex.sub_im, hci] at h
    have := abs_le.mp (h.trans hδ)
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hfin := Z.finite_window (T - 1) (2 * T + 1)
  have hfinB : (Z.carrier ∩ Metric.closedBall c δ).Finite := hfin.subset hsub
  unfold discCount
  rw [finsum_mem_eq_finite_toFinset_sum _ hfinB, ← Finset.sum_filter]
  congr 1
  ext ρ
  simp only [Set.Finite.mem_toFinset, Finset.mem_filter]
  exact ⟨fun h => ⟨hsub h, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩

/-- **The local count holds in measure.**  For `0 < δ ≤ ½`, `C > 0`, `T > 1`, the heights
`t ∈ [T, 2T]` whose disc about `½ + δ + it` holds more than `C(δ log t + 1)` zeros have measure at
most
`2N(T − 1, 2T + 1)/(C log T)`.  Each zero lies in the disc for a set of `t` of length `≤ 2δ`
(Fubini), and Markov's inequality divides by `C(δ log T + 1) ≥ Cδ log T`. -/
theorem volume_localCount_gt_le (Z : ZeroConfig) {δ C T : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (hC : 0 < C) (hT : 1 < T) :
    MeasureTheory.volume {t ∈ Icc T (2 * T) |
        C * (δ * Real.log t + 1) < discCount Z (((1 / 2 + δ : ℝ) : ℂ) + (t : ℂ) * I) δ}
      ≤ ENNReal.ofReal (2 * Z.N (T - 1) (2 * T + 1) / (C * Real.log T)) := by
  set F := (Z.finite_window (T - 1) (2 * T + 1)).toFinset with hF
  set c : ℝ → ℂ := fun t => ((1 / 2 + δ : ℝ) : ℂ) + (t : ℂ) * I with hc
  set B : ℂ → Set ℝ := fun ρ => {t | ρ ∈ Metric.closedBall (c t) δ} with hBdef
  have hcont : Continuous c := by rw [hc]; fun_prop
  have hB : ∀ ρ, MeasurableSet (B ρ) := fun ρ =>
    (isClosed_le (continuous_const.dist hcont) continuous_const).measurableSet
  have hBsub : ∀ ρ, B ρ ⊆ Icc (ρ.im - δ) (ρ.im + δ) := by
    intro ρ t ht
    have hd : ‖ρ - c t‖ ≤ δ := by rw [← Complex.dist_eq]; exact Metric.mem_closedBall.mp ht
    have h := (Complex.abs_im_le_norm (ρ - c t)).trans hd
    have hci : (c t).im = t := by simp [hc]
    rw [Complex.sub_im, hci] at h
    have := abs_le.mp h
    exact ⟨by linarith, by linarith⟩
  set g : ℝ → ENNReal := fun t => ∑ ρ ∈ F, (B ρ).indicator (fun _ => (Z.mult ρ : ENNReal)) t with hg
  have hgm : Measurable g := Finset.measurable_sum _ fun ρ _ => measurable_const.indicator (hB ρ)
  have hcount : ∀ t ∈ Icc T (2 * T), ((discCount Z (c t) δ : ℕ) : ENNReal) = g t := by
    intro t ht
    rw [discCount_eq_sum Z hδ ht, hg, Nat.cast_sum]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    simp only [Set.indicator_apply, hBdef, Set.mem_setOf_eq]
    split_ifs <;> simp
  have hint : ∫⁻ t in Icc T (2 * T), g t
      ≤ ∑ ρ ∈ F, (Z.mult ρ : ENNReal) * ENNReal.ofReal (2 * δ) := by
    rw [hg, MeasureTheory.lintegral_finsetSum _ fun ρ _ => measurable_const.indicator (hB ρ)]
    refine Finset.sum_le_sum fun ρ _ => ?_
    rw [MeasureTheory.lintegral_indicator_const (hB ρ)]
    gcongr
    calc (MeasureTheory.volume.restrict (Icc T (2 * T))) (B ρ) ≤ MeasureTheory.volume (B ρ) :=
          MeasureTheory.Measure.restrict_le_self _
      _ ≤ MeasureTheory.volume (Icc (ρ.im - δ) (ρ.im + δ)) := MeasureTheory.measure_mono (hBsub ρ)
      _ = ENNReal.ofReal (2 * δ) := by rw [Real.volume_Icc]; ring_nf
  have hL : 0 < Real.log T := Real.log_pos hT
  set M : ℝ := C * (δ * Real.log T + 1) with hM
  have hM0 : 0 < M := by positivity
  have hset : {t ∈ Icc T (2 * T) | C * (δ * Real.log t + 1) < discCount Z (c t) δ}
      ⊆ {t | ENNReal.ofReal M ≤ g t} ∩ Icc T (2 * T) := by
    rintro t ⟨ht, hlt⟩
    refine ⟨?_, ht⟩
    have hlog : Real.log T ≤ Real.log t := Real.log_le_log (by linarith) ht.1
    have hMle : M ≤ (discCount Z (c t) δ : ℝ) := by
      have : M ≤ C * (δ * Real.log t + 1) := by
        rw [hM]; gcongr
      linarith
    show ENNReal.ofReal M ≤ g t
    rw [← hcount t ht, ← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hMle
  have hN : (Z.N (T - 1) (2 * T + 1) : ℝ) = ∑ ρ ∈ F, (Z.mult ρ : ℝ) := by
    rw [ZeroConfig.N, ZeroConfig.window, finsum_mem_eq_finite_toFinset_sum _
      (Z.finite_window (T - 1) (2 * T + 1)), Nat.cast_sum]
  have hsumF : ∑ ρ ∈ F, (Z.mult ρ : ENNReal) * ENNReal.ofReal (2 * δ)
      = ENNReal.ofReal (2 * δ * Z.N (T - 1) (2 * T + 1)) := by
    rw [hN, Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg fun ρ _ => by positivity]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [show ENNReal.ofReal (2 * δ * (Z.mult ρ : ℝ))
        = ENNReal.ofReal (2 * δ) * (Z.mult ρ : ENNReal) by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast], mul_comm]
  calc MeasureTheory.volume {t ∈ Icc T (2 * T) | C * (δ * Real.log t + 1) < discCount Z (c t) δ}
      ≤ MeasureTheory.volume ({t | ENNReal.ofReal M ≤ g t} ∩ Icc T (2 * T)) :=
        MeasureTheory.measure_mono hset
    _ = (MeasureTheory.volume.restrict (Icc T (2 * T))) {t | ENNReal.ofReal M ≤ g t} :=
        (MeasureTheory.Measure.restrict_apply' measurableSet_Icc).symm
    _ ≤ (∫⁻ t in Icc T (2 * T), g t) / ENNReal.ofReal M :=
        MeasureTheory.meas_ge_le_lintegral_div hgm.aemeasurable
          (by simpa using hM0) ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (2 * δ * Z.N (T - 1) (2 * T + 1)) / ENNReal.ofReal M := by
        rw [← hsumF]; gcongr
    _ = ENNReal.ofReal (2 * δ * Z.N (T - 1) (2 * T + 1) / M) :=
        (ENNReal.ofReal_div_of_pos hM0).symm
    _ ≤ ENNReal.ofReal (2 * Z.N (T - 1) (2 * T + 1) / (C * Real.log T)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hN0 : (0 : ℝ) ≤ Z.N (T - 1) (2 * T + 1) := Nat.cast_nonneg _
        rw [div_le_div_iff₀ hM0 (by positivity), hM]
        nlinarith [mul_nonneg (mul_nonneg hN0 hδ0.le) hC.le]

/-- Riemann–von Mangoldt bounds the window `(T − 1, 2T + 1]`:
`N(T − 1, 2T + 1) ≤ (T/2π) log T + K log T` for all large `T`. -/
theorem exists_N_window_le {Z : ZeroConfig} (hZ : RiemannVonMangoldt Z) :
    ∃ K : ℝ, ∀ᶠ T in Filter.atTop,
      (Z.N (T - 1) (2 * T + 1) : ℝ) ≤ T / (2 * Real.pi) * Real.log T + K * Real.log T := by
  obtain ⟨C₀, T₀, hC₀⟩ := hZ.main
  obtain ⟨A₀, hA₀, hloc⟩ := hZ.local_count
  refine ⟨|C₀| + 4 * A₀, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (max T₀ 3)] with T hT
  have hT₀ : T₀ ≤ T := le_trans (le_max_left _ _) hT
  have hT3 : 3 ≤ T := le_trans (le_max_right _ _) hT
  have hL : 1 < Real.log T := by
    rw [← Real.log_exp 1]
    exact Real.log_lt_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have hsplit : (Z.N (T - 1) (2 * T + 1) : ℝ) =
      Z.N (T - 1) T + Z.N T (2 * T) + Z.N (2 * T) (2 * T + 1) := by
    rw [Assembly.N_add Z (by linarith : T - 1 ≤ 2 * T) (by linarith),
      Assembly.N_add Z (by linarith : T - 1 ≤ T) (by linarith)]
    push_cast; ring
  have h1 := hloc (T - 1)
  rw [sub_add_cancel] at h1
  have h3 := hloc (2 * T)
  have h2 := hC₀ T hT₀
  rw [abs_le] at h2
  have hlog1 : Real.log (|T - 1| + 3) ≤ 2 * Real.log T := by
    rw [abs_of_pos (by linarith), ← Real.log_rpow (by linarith)]
    refine Real.log_le_log (by linarith) ?_
    rw [show (T : ℝ) ^ (2 : ℝ) = T ^ 2 by norm_cast]; nlinarith
  have hlog3 : Real.log (|2 * T| + 3) ≤ 2 * Real.log T := by
    rw [abs_of_pos (by linarith), ← Real.log_rpow (by linarith)]
    refine Real.log_le_log (by linarith) ?_
    rw [show (T : ℝ) ^ (2 : ℝ) = T ^ 2 by norm_cast]; nlinarith
  have hell : ell1 T ≤ Real.log T := by
    have hl : l T ≤ Real.log T - Real.log (2 * Real.pi) := by
      rw [l, Real.log_div (by linarith) (by positivity)]
    have hlog2 : 2 * Real.log 2 - 1 ≤ Real.log (2 * Real.pi) := by
      have h4 : 2 * Real.log 2 = Real.log 4 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      have : Real.log 4 ≤ Real.log (2 * Real.pi) + 1 := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 / (2 * Real.pi) by positivity)
        rw [Real.log_div (by norm_num) (by positivity)] at this
        have h45 : 4 / (2 * Real.pi) ≤ 1 := by
          rw [div_le_one (by positivity)]; linarith [Real.pi_gt_three]
        linarith
      linarith
    rw [ell1]; linarith
  have hC₀abs : C₀ ≤ |C₀| := le_abs_self C₀
  have hT2π : 0 ≤ T / (2 * Real.pi) := by positivity
  have hm := mul_le_mul_of_nonneg_left hell hT2π
  have hL0 : 0 ≤ Real.log T := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hlog1 (by linarith : (0 : ℝ) ≤ A₀),
    mul_le_mul_of_nonneg_left hlog3 (by linarith : (0 : ℝ) ≤ A₀),
    mul_le_mul_of_nonneg_right hC₀abs hL0]

/-- **Riemann–von Mangoldt gives the local count off a set of proportion `1/(πC)`.**  For every
`0 < δ ≤ ½` and `C > 0` there is `K` with, for all large `T`,
`|{t ∈ [T, 2T] : #disc(½ + δ + it, δ) > C(δ log t + 1)}| ≤ T/(πC) + K`. -/
theorem eventually_volume_localCount_gt_le {Z : ZeroConfig} (hZ : RiemannVonMangoldt Z)
    {δ C : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (hC : 0 < C) :
    ∃ K : ℝ, ∀ᶠ T in Filter.atTop, MeasureTheory.volume {t ∈ Icc T (2 * T) |
        C * (δ * Real.log t + 1) < discCount Z (((1 / 2 + δ : ℝ) : ℂ) + (t : ℂ) * I) δ}
      ≤ ENNReal.ofReal (T / (Real.pi * C) + K) := by
  obtain ⟨K, hK⟩ := exists_N_window_le hZ
  refine ⟨2 * K / C, ?_⟩
  filter_upwards [hK, Filter.eventually_ge_atTop (3 : ℝ)] with T hN hT3
  have hL : 1 < Real.log T := by
    rw [← Real.log_exp 1]
    exact Real.log_lt_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  refine (volume_localCount_gt_le Z hδ0 hδ hC (by linarith)).trans (ENNReal.ofReal_le_ofReal ?_)
  have hL0 : 0 < Real.log T := by linarith
  rw [div_le_iff₀ (by positivity)]
  have e : (T / (Real.pi * C) + 2 * K / C) * (C * Real.log T)
      = 2 * (T / (2 * Real.pi) * Real.log T + K * Real.log T) := by
    field_simp
  rw [e]
  linarith

end

end RHTower.LocalCountFalsifier
