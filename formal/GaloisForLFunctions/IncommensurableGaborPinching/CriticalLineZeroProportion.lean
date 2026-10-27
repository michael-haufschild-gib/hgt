import GaloisForLFunctions.IncommensurableGaborPinching.CosineKernelNonLatticeFloor
import GaloisForLFunctions.RHTower.HorizontallyIsolatedSimpleZeros
import GaloisForLFunctions.RHTower.ZetaOffLineMomentMontgomeryTaylor

/-!
# Unconditional critical-line zero proportion strictly beyond the Montgomery–Taylor constant

Alpöge and Furman (`Zeta23`, Theorem D) establish the unconditional lower bounds
`HD(1) = 3/2 − cot(1/√2)/√2 = 0.6725007036…` for the proportion of simple critical-line zeros of
`ζ(s)` and `GD(1) = (HD(1) + 1)/2 = 0.8362503518…` for the proportion of distinct zeros of `ζ(s)`.
In their rank–trace inequality (`Zeta23/ZeroSide/RankTraceMult.lean`), the simple critical-line
summand `P₁ = ∑_{z ∈ S₁} w_z w_zᵀ` (`‖w_z‖₂² ≤ 1`) is bounded solely via diagonal trace
dominance `‖P₁‖_F² ≤ tr P₁ ≤ s₁`, which attains equality if and only if the evaluation vectors
`(w_z)_{z ∈ S₁}` are pairwise orthogonal.

For the boxcar window (`sin(π Δ)/(π Δ)`), pairwise orthogonality on the critical line is
realizable in principle when ordinates lie on a shift of the uniform `2π/L`-lattice (`Δ ∈ ℤ \ {0}`).
For the Montgomery–Taylor cosine window `v*_λ(v) = cos(√2 λ v)`, however, the correlation kernel
`mtKernel` vanishes only inside two narrow intervals `I₁ = (26/25, 43/40)` and
`I₂ = (503/250, 256/125)` on `[0, 3]` whose sumsets are disjoint from `I₁ ∪ I₂`
(`CosineKernelNonLatticeFloor.lean`). Consequently, no three simple critical-line ordinates in a
short window `α (γ₃ − γ₁) ≤ 3` can be mutually orthogonal!

Combining:
1. **Consecutive-triple packing (`exists_disjoint_short_triples`):** since the baseline proportion
   `HD(λ) > 2/3` exceeds `2/3` by a positive margin (`HD(1) − 2/3 > 0.0058`), telescoping consecutive
   ordinate spans and partitioning indices modulo `3` produces `≥ N / 625` vertex-disjoint triples
   of bulk simple critical-line zeros of scaled span `≤ 3`;
2. **Incommensurable Gabor pinching (`exists_pair_mtKernel_ge_of_triple` +
   `eventually_pairGridOverlap_atD_close`):** each triple yields a distinct pair with finite-grid
   overlap `|pairGridOverlap| ≥ 1/500`, contributing `2 · ∑ overlap² ≥ 10⁻⁸ · N(T, 2T)` of
   strictly positive off-diagonal Frobenius energy;
3. **Disjoint-pair Schur–Jensen slack (`seamA_mult2_disjointPairs`,
   `seamA_mult3_disjointPairs`):** this off-diagonal Frobenius slack enters the `c = 2` and `c = 3`
   rank–trace seams directly with positive sign, strictly improving the asymptotic simple
   critical-line proportion to `HD(1) + 10⁻⁸` (`≥ 67250071 / 100000000 > 67.250071%`) and the
   distinct-zero proportion to `GD(1) + (1/2) · 10⁻⁸`.
-/

noncomputable section

open Real Filter Asymptotics Topology Finset Zeta23 Zeta23.ZeroSide Zeta23.Assembly Zeta23.ThmD
open GaloisForLFunctions.HTGeometry
open scoped BigOperators

namespace GaloisForLFunctions.IncommensurableGaborPinching

/-! ## Section 1. Combinatorial consecutive-triple packing -/

/-- **Pigeonhole packing of vertex-disjoint short triples.**
Given `m ≥ 3` strictly increasing real numbers `g : Fin m → ℝ` in `[a, b]` and a positive scale
`α > 0`, telescoping `(g(j+2) − g(j)) = (g(j+1) − g(j)) + (g(j+2) − g(j+1))` and selecting the
largest residue class modulo `3` yields a set `R ⊆ {0, …, m − 3}` of pairwise `3`-separated indices
with `9 · #R ≥ 3(m − 2) − 2 α (b − a)` such that `α (g(j+2) − g(j)) ≤ 3` for every `j ∈ R`. -/
theorem exists_disjoint_short_triples {m : ℕ} (hm : 3 ≤ m)
    {g : Fin m → ℝ} (hg : StrictMono g) {a b α : ℝ}
    (hab : a ≤ b) (hα : 0 < α)
    (hbounds : ∀ i : Fin m, a ≤ g i ∧ g i ≤ b) :
    ∃ (R : Finset ℕ) (hR : ∀ j ∈ R, j + 2 < m),
      3 * ((m - 2 : ℕ) : ℝ) - 2 * α * (b - a) ≤ 9 * (R.card : ℝ) ∧
      (∀ j (hj : j ∈ R), α * (g ⟨j + 2, hR j hj⟩ - g ⟨j, by have := hR j hj; omega⟩) ≤ 3) ∧
      ∀ j₁ ∈ R, ∀ j₂ ∈ R, j₁ ≠ j₂ → j₁ + 2 < j₂ ∨ j₂ + 2 < j₁ := by
  set k : ℕ := m - 2
  set G : ℕ → ℝ := fun j => if h : j < m then g ⟨j, h⟩ else b
  have hG_mono : ∀ j : ℕ, G j ≤ G (j + 1) := fun j => by
    by_cases h1 : j + 1 < m
    · have h0 : j < m := by omega
      simp only [G, dif_pos h0, dif_pos h1]
      exact (hg (Fin.mk_lt_mk.mpr (by omega))).le
    · by_cases h0 : j < m
      · simp only [G, dif_pos h0, dif_neg h1]
        exact (hbounds ⟨j, h0⟩).2
      · simp only [G, dif_neg h0, dif_neg h1]
        exact le_rfl
  have hG_bounds : ∀ j : ℕ, a ≤ G j ∧ G j ≤ b := fun j => by
    by_cases h : j < m
    · simp only [G, dif_pos h]
      exact hbounds ⟨j, h⟩
    · simp only [G, dif_neg h]
      exact ⟨hab, le_rfl⟩
  have htel : ∀ s n : ℕ, ∑ j ∈ Finset.range n, (G (s + j + 1) - G (s + j)) = G (s + n) - G s := by
    intro s n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, show s + (n + 1) = s + n + 1 by omega]
      ring
  have hsum_span : ∑ j ∈ Finset.range k, α * (G (j + 2) - G j) ≤ 2 * α * (b - a) := by
    have hsplit : ∑ j ∈ Finset.range k, (G (j + 2) - G j)
        = (∑ j ∈ Finset.range k, (G (0 + j + 1) - G (0 + j)))
          + ∑ j ∈ Finset.range k, (G (1 + j + 1) - G (1 + j)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [zero_add, show 1 + j + 1 = j + 2 by omega, show 1 + j = j + 1 by omega]
      ring
    rw [htel 0 k, htel 1 k] at hsplit
    have hb0 : G (0 + k) - G 0 ≤ b - a := by linarith [(hG_bounds (0 + k)).2, (hG_bounds 0).1]
    have hb1 : G (1 + k) - G 1 ≤ b - a := by linarith [(hG_bounds (1 + k)).2, (hG_bounds 1).1]
    rw [← Finset.mul_sum]
    have htot : ∑ j ∈ Finset.range k, (G (j + 2) - G j) ≤ 2 * (b - a) := by linarith
    calc α * ∑ j ∈ Finset.range k, (G (j + 2) - G j)
        ≤ α * (2 * (b - a)) := mul_le_mul_of_nonneg_left htot hα.le
      _ = 2 * α * (b - a) := by ring
  set Good := (Finset.range k).filter (fun j => α * (G (j + 2) - G j) ≤ 3)
  set Bad := (Finset.range k).filter (fun j => ¬ (α * (G (j + 2) - G j) ≤ 3))
  have hcard_split : Good.card + Bad.card = k := by
    simp only [Good, Bad]
    rw [Finset.card_filter_add_card_filter_not, Finset.card_range]
  have hnn : ∀ j : ℕ, 0 ≤ α * (G (j + 2) - G j) := fun j =>
    mul_nonneg hα.le (sub_nonneg.mpr ((hG_mono j).trans (hG_mono (j + 1))))
  have hbad_le : 3 * (Bad.card : ℝ) ≤ 2 * α * (b - a) := by
    calc 3 * (Bad.card : ℝ) = ∑ _ ∈ Bad, (3 : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ j ∈ Bad, α * (G (j + 2) - G j) := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hnot := (Finset.mem_filter.mp hj).2
          linarith
      _ ≤ ∑ j ∈ Finset.range k, α * (G (j + 2) - G j) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun j _ _ => hnn j)
      _ ≤ 2 * α * (b - a) := hsum_span
  set R₀ := Good.filter (fun j => j % 3 = 0)
  set R₁ := Good.filter (fun j => j % 3 = 1)
  set R₂ := Good.filter (fun j => j % 3 = 2)
  have hsub3 : Good ⊆ R₀ ∪ (R₁ ∪ R₂) := by
    intro j hj
    simp only [R₀, R₁, R₂, Finset.mem_union, Finset.mem_filter]
    have hmod : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
    tauto
  have hcard3 : Good.card ≤ R₀.card + R₁.card + R₂.card := by
    calc Good.card ≤ (R₀ ∪ (R₁ ∪ R₂)).card := Finset.card_le_card hsub3
      _ ≤ R₀.card + (R₁ ∪ R₂).card := Finset.card_union_le _ _
      _ ≤ R₀.card + (R₁.card + R₂.card) := Nat.add_le_add_left (Finset.card_union_le _ _) _
      _ = R₀.card + R₁.card + R₂.card := by omega
  have hex_r : ∃ r₀ : ℕ, Good.card ≤ 3 * (Good.filter (fun j => j % 3 = r₀)).card := by
    by_cases h0 : Good.card ≤ 3 * R₀.card
    · exact ⟨0, h0⟩
    · by_cases h1 : Good.card ≤ 3 * R₁.card
      · exact ⟨1, h1⟩
      · refine ⟨2, ?_⟩
        change Good.card ≤ 3 * R₂.card
        omega
  obtain ⟨r₀, hr₀⟩ := hex_r
  set R := Good.filter (fun j => j % 3 = r₀)
  have hR_lt : ∀ j ∈ R, j + 2 < m := by
    intro j hj
    have hjG := (Finset.mem_filter.mp hj).1
    have hjk := Finset.mem_range.mp (Finset.mem_filter.mp hjG).1
    omega
  refine ⟨R, hR_lt, ?_, ?_, ?_⟩
  · have hr_real : (Good.card : ℝ) ≤ 3 * (R.card : ℝ) := by exact_mod_cast hr₀
    have hsplit_real : (Good.card : ℝ) + (Bad.card : ℝ) = ((m - 2 : ℕ) : ℝ) := by
      exact_mod_cast hcard_split
    linarith
  · intro j hj
    have hjG := (Finset.mem_filter.mp hj).1
    have hle3 := (Finset.mem_filter.mp hjG).2
    have h2 : j + 2 < m := hR_lt j hj
    have h0 : j < m := by omega
    simpa only [G, dif_pos h2, dif_pos h0] using hle3
  · intro j₁ hj₁ j₂ hj₂ hne
    have m1 : j₁ % 3 = r₀ := (Finset.mem_filter.mp hj₁).2
    have m2 : j₂ % 3 = r₀ := (Finset.mem_filter.mp hj₂).2
    omega

/-- Lifting `exists_pair_mtKernel_ge_of_triple` from real ordinates to a triple of elements. -/
lemma exists_pair_in_triple_mtKernel_ge {α : Type*} [DecidableEq α]
    {lam α₀ : ℝ} (hlo : 999 / 1000 ≤ lam) (hhi : lam ≤ 1) (hα : 0 < α₀)
    (im : α → ℝ) {z₁ z₂ z₃ : α}
    (h12 : im z₁ < im z₂) (h23 : im z₂ < im z₃)
    (hspan : α₀ * (im z₃ - im z₁) ≤ 3) :
    ∃ x y : α, x ∈ ({z₁, z₂, z₃} : Finset α) ∧ y ∈ ({z₁, z₂, z₃} : Finset α) ∧
      x ≠ y ∧ 1 / 250 ≤ |mtKernel lam (α₀ * |im x - im y|)| := by
  obtain ⟨u, v, hu, hv, huv, hK⟩ :=
    exists_pair_mtKernel_ge_of_triple hlo hhi hα h12 h23 hspan
  have hx : ∃ x ∈ ({z₁, z₂, z₃} : Finset α), im x = u := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl | rfl
    · exact ⟨z₁, by simp, rfl⟩
    · exact ⟨z₂, by simp, rfl⟩
    · exact ⟨z₃, by simp, rfl⟩
  have hy : ∃ y ∈ ({z₁, z₂, z₃} : Finset α), im y = v := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl
    · exact ⟨z₁, by simp, rfl⟩
    · exact ⟨z₂, by simp, rfl⟩
    · exact ⟨z₃, by simp, rfl⟩
  obtain ⟨x, hx_mem, hxim⟩ := hx
  obtain ⟨y, hy_mem, hyim⟩ := hy
  refine ⟨x, y, hx_mem, hy_mem, fun hxy => huv (by rw [← hxim, ← hyim, hxy]), ?_⟩
  have habs : mtKernel lam (α₀ * |im x - im y|) = mtKernel lam (α₀ * (v - u)) := by
    rw [hxim, hyim, abs_sub_comm]
    have : α₀ * |v - u| = |α₀ * (v - u)| := by rw [abs_mul, abs_of_pos hα]
    rw [this, mtKernel_abs]
  rwa [habs]

/-! ## Section 2. Bulk simple critical-line census and scale bounds -/

/-- The subset of `S₁` (simple critical-line zeros in `ZI Z T`) lying strictly inside the bulk
interval `(T + √T, 2T − √T]`. -/
def S₁Bulk (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hconj : PhiHatConj T (P.atD T)) : Finset (ZI Z T) :=
  ((blockData Z T (P.atD T) hconj).S₁).filter
    (fun z => T + Real.sqrt T < (z : ℂ).im ∧ (z : ℂ).im ≤ 2 * T - Real.sqrt T)

private lemma N_add_nat_le (Z : ZeroConfig) (t C : ℝ) (_ : 0 ≤ C) (k : ℕ)
    (hunit : ∀ j < k, (Z.N (t + j) (t + j + 1) : ℝ) ≤ C) :
    (Z.N t (t + k) : ℝ) ≤ k * C := by
  induction k with
  | zero =>
    simp only [Nat.cast_zero, add_zero, zero_mul, N_self]
    exact le_rfl
  | succ n ih =>
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hsplit : Z.N t (t + ((n + 1 : ℕ) : ℝ))
        = Z.N t (t + n) + Z.N (t + n) (t + ((n + 1 : ℕ) : ℝ)) :=
      N_add Z (by linarith) (by push_cast; linarith)
    have hcast : ((Z.N t (t + ((n + 1 : ℕ) : ℝ)) : ℕ) : ℝ)
        = (Z.N t (t + n) : ℝ) + (Z.N (t + n) (t + n + 1) : ℝ) := by
      rw [hsplit]
      push_cast
      rw [show t + ((n : ℝ) + 1) = t + (n : ℝ) + 1 by ring]
    rw [hcast]
    have h1 := ih (fun j hj => hunit j (Nat.lt_succ_of_lt hj))
    have h2 := hunit n (Nat.lt_succ_self n)
    push_cast
    linarith

private lemma N_mono_right (Z : ZeroConfig) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    Z.N a b ≤ Z.N a c := by
  rw [N_add Z hab hbc]
  exact Nat.le_add_right _ _

private lemma N_mono_left (Z : ZeroConfig) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    Z.N b c ≤ Z.N a c := by
  rw [N_add Z hab hbc]
  exact Nat.le_add_left _ _

/-- Decomposition of `N₀ˢ(T, 2T)` into `S₁Bulk` plus the two `√T` boundary strips. -/
lemma N0s_le_card_S₁Bulk_add_boundary (Z : ZeroConfig) (P : Params) {T : ℝ}
    (hT : 4 ≤ T) (hconj : PhiHatConj T (P.atD T)) :
    Z.N0s T (2 * T) ≤ (S₁Bulk Z P T hconj).card
      + Z.N T (T + Real.sqrt T) + Z.N (2 * T - Real.sqrt T) (2 * T) := by
  have hs_nn : 0 ≤ Real.sqrt T := Real.sqrt_nonneg T
  have h2s : 2 * Real.sqrt T ≤ T := by
    have hsq : (2 * Real.sqrt T) ^ 2 ≤ T ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by linarith)]
      nlinarith
    nlinarith [sq_nonneg (T - 2 * Real.sqrt T)]
  have hsplit1 := N0s_add Z (a := T) (b := T + Real.sqrt T) (c := 2 * T)
    (by linarith) (by linarith)
  have hsplit2 := N0s_add Z (a := T + Real.sqrt T) (b := 2 * T - Real.sqrt T) (c := 2 * T)
    (by linarith) (by linarith)
  have hlo : Z.N0s T (T + Real.sqrt T) ≤ Z.N T (T + Real.sqrt T) := by
    have tc := Z.trivial_chain T (T + Real.sqrt T)
    exact tc.1.trans (tc.2.1.trans tc.2.2.1)
  have hhi : Z.N0s (2 * T - Real.sqrt T) (2 * T) ≤ Z.N (2 * T - Real.sqrt T) (2 * T) := by
    have tc := Z.trivial_chain (2 * T - Real.sqrt T) (2 * T)
    exact tc.1.trans (tc.2.1.trans tc.2.2.1)
  have hmid : Z.N0s (T + Real.sqrt T) (2 * T - Real.sqrt T) ≤ (S₁Bulk Z P T hconj).card := by
    set W : Set ℂ := Z.window (T + Real.sqrt T) (2 * T - Real.sqrt T) ∩ ZeroConfig.onLine ∩ Z.simple
    change W.ncard ≤ (S₁Bulk Z P T hconj).card
    set img : Finset ℂ := (S₁Bulk Z P T hconj).image (fun z : ZI Z T => (z : ℂ))
    have hinj : Function.Injective (fun z : ZI Z T => (z : ℂ)) := Subtype.val_injective
    have hcard_img : ((img : Set ℂ).ncard) = (S₁Bulk Z P T hconj).card := by
      rw [Set.ncard_coe_finset, Finset.card_image_of_injective _ hinj]
    rw [← hcard_img]
    refine Set.ncard_le_ncard ?_ img.finite_toSet
    intro ρ hρ
    rcases hρ with ⟨⟨⟨hcar, him_lo, him_hi⟩, hon⟩, hsimp⟩
    have hD0 : 0 ≤ D0 T := D0_nonneg T
    have hZI : ρ ∈ ZI Z T := by
      rw [mem_ZI, mem_ZIprime_iff]
      exact ⟨hcar, by linarith, by linarith⟩
    rw [Finset.mem_coe, Finset.mem_image]
    refine ⟨⟨ρ, hZI⟩, ?_, rfl⟩
    simp only [S₁Bulk, ZeroBlockData.S₁, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨⟨?_, hsimp⟩, him_lo, him_hi⟩
    dsimp only [blockData]
    rwa [mkData_σ_eq_iff]
  omega

/-- The combined count in `(T, T + √T] ∪ (2T − √T, 2T]` is `O(√T l(T)) = o(N(T, 2T))`. -/
lemma isLittleO_boundary_N (Z : ZeroConfig) (hRvM : RiemannVonMangoldt Z) :
    (fun T => ((Z.N T (T + Real.sqrt T) + Z.N (2 * T - Real.sqrt T) (2 * T) : ℕ) : ℝ))
      =o[atTop] (fun T => (Z.N T (2 * T) : ℝ)) := by
  obtain ⟨A₀, hA₀, hloc⟩ := hRvM.local_count
  have hO : (fun T => ((Z.N T (T + Real.sqrt T) + Z.N (2 * T - Real.sqrt T) (2 * T) : ℕ) : ℝ))
      =O[atTop] (fun T => Real.sqrt T * l T) := by
    refine IsBigO.of_bound (8 * A₀) ?_
    filter_upwards [eventually_ge_atTop Tail.T₀, eventually_l_pos] with T hT hl
    have hT300 : (300 : ℝ) ≤ T := hT
    have hs_ge : 17 ≤ Real.sqrt T := by
      rw [Real.le_sqrt (by norm_num) (by linarith)]
      linarith
    have hs_le_T : Real.sqrt T + 4 ≤ T := by
      have hsq : Real.sqrt T ^ 2 = T := Real.sq_sqrt (by linarith)
      nlinarith
    set k : ℕ := ⌈Real.sqrt T⌉₊
    have hk_ge : Real.sqrt T ≤ (k : ℝ) := Nat.le_ceil _
    have hk_lt : (k : ℝ) < Real.sqrt T + 1 := Nat.ceil_lt_add_one (by positivity)
    have hk_le_2s : (k : ℝ) ≤ 2 * Real.sqrt T := by linarith
    have hlog4 : Real.log (4 * T) ≤ 2 * l T := Tail.log_four_mul_le_two_mul_l hT
    set C : ℝ := 2 * A₀ * l T
    have hC_nn : 0 ≤ C := by positivity
    have hunit_bound : ∀ t : ℝ, 0 ≤ t → t ≤ 3 * T → (Z.N t (t + 1) : ℝ) ≤ C := by
      intro t ht0 ht3
      calc (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3) := hloc t
        _ ≤ A₀ * Real.log (4 * T) := by
            apply mul_le_mul_of_nonneg_left _ (by linarith)
            apply Real.log_le_log (by positivity)
            rw [abs_of_nonneg ht0]
            linarith
        _ ≤ A₀ * (2 * l T) := mul_le_mul_of_nonneg_left hlog4 (by linarith)
        _ = C := by ring
    have h1 : (Z.N T (T + Real.sqrt T) : ℝ) ≤ (k : ℝ) * C := by
      have hm : Z.N T (T + Real.sqrt T) ≤ Z.N T (T + k) :=
        N_mono_right Z (by linarith) (by linarith)
      refine le_trans (by exact_mod_cast hm) (N_add_nat_le Z T C hC_nn k fun j hj => ?_)
      have hj_le : (j : ℝ) ≤ k := by exact_mod_cast hj.le
      exact hunit_bound (T + j) (by positivity) (by linarith)
    have h2 : (Z.N (2 * T - Real.sqrt T) (2 * T) : ℝ) ≤ (k : ℝ) * C := by
      have hm : Z.N (2 * T - Real.sqrt T) (2 * T) ≤ Z.N (2 * T - k) (2 * T - k + k) := by
        rw [sub_add_cancel]
        exact N_mono_left Z (by linarith) (by linarith)
      refine le_trans (by exact_mod_cast hm) (N_add_nat_le Z (2 * T - k) C hC_nn k fun j hj => ?_)
      have hj_le : (j : ℝ) ≤ k := by exact_mod_cast hj.le
      have hj_nn : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      exact hunit_bound (2 * T - k + j) (by linarith) (by linarith)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
      abs_of_nonneg (by positivity)]
    push_cast
    have hkC : (k : ℝ) * C ≤ 2 * Real.sqrt T * C := mul_le_mul_of_nonneg_right hk_le_2s hC_nn
    simp only [C] at hkC h1 h2
    linarith
  exact hO.trans_isLittleO (isLittleO_N_of_isLittleO_Tl Z hRvM isLittleO_sqrt_mul_l_Tl)

/-- For any fixed `λ < 1`, `P.L T · T / (2π) ≤ N(T, 2T)` eventually by Riemann–von Mangoldt. -/
lemma eventually_L_mul_T_div_two_pi_le_N (Z : ZeroConfig) (hRvM : RiemannVonMangoldt Z)
    {P : Params} (hlam0 : 0 < P.lam) (hlam1 : P.lam < 1) :
    ∀ᶠ T in atTop, P.L T * T / (2 * Real.pi) ≤ (Z.N T (2 * T) : ℝ) := by
  obtain ⟨C, T₀, hmain⟩ := hRvM.main
  set δ : ℝ := 1 - P.lam
  have hδ : 0 < δ := by simp only [δ]; linarith
  filter_upwards [eventually_ge_atTop T₀, eventually_log_le_two_l, eventually_log_nonneg,
    eventually_l_pos, eventually_ge_atTop ((4 * Real.pi * |C| + 1) / δ), eventually_ge_atTop 0]
    with T hT hlog hlog0 hl hTδ hT0
  have h1 := (abs_le.mp (hmain T hT)).1
  have hc := c₀_pos
  have hℓ : l T ≤ ell1 T := by rw [ell1_eq]; linarith
  have h3 : T / (2 * Real.pi) * l T ≤ T / (2 * Real.pi) * ell1 T :=
    mul_le_mul_of_nonneg_left hℓ (by positivity)
  have hlog_bd : C * Real.log T ≤ 2 * |C| * l T := by
    calc C * Real.log T ≤ |C| * Real.log T := mul_le_mul_of_nonneg_right (le_abs_self C) hlog0
      _ ≤ |C| * (2 * l T) := mul_le_mul_of_nonneg_left hlog (abs_nonneg C)
      _ = 2 * |C| * l T := by ring
  have hδT : 4 * Real.pi * |C| ≤ δ * T := by
    have := (div_le_iff₀ hδ).mp hTδ
    linarith
  have hgap : 2 * |C| * l T ≤ δ * (T / (2 * Real.pi) * l T) := by
    have hdiv : 2 * |C| ≤ δ * (T / (2 * Real.pi)) := by
      rw [← mul_div_assoc, le_div_iff₀ (by positivity)]
      linarith
    calc 2 * |C| * l T ≤ (δ * (T / (2 * Real.pi))) * l T :=
          mul_le_mul_of_nonneg_right hdiv hl.le
      _ = δ * (T / (2 * Real.pi) * l T) := by ring
  have hL_eq : P.L T * T / (2 * Real.pi) = (1 - δ) * (T / (2 * Real.pi) * l T) := by
    simp only [Params.L, δ]
    ring
  linarith

/-- Quantitative Lipschitz lower bound `HD(1) − HD(λ) ≤ 56 π² (1 − λ)` on `[1/2, 1]`. -/
lemma HD_one_sub_HD_le {lam : ℝ} (hl05 : 1 / 2 ≤ lam) (hl1 : lam ≤ 1) :
    HD 1 - HD lam ≤ 56 * Real.pi ^ 2 * (1 - lam) := by
  have hl0 : (0 : ℝ) ≤ lam := by linarith
  have hclb := cStar_ge_lb hl05 hl1
  have hclb1 := cStar_ge_lb (by norm_num : (1 : ℝ) / 2 ≤ 1) le_rfl
  have hc0 : (0 : ℝ) < cStar lam := lt_of_lt_of_le (by positivity) hclb
  have hc1 : (0 : ℝ) < cStar 1 := lt_of_lt_of_le (by positivity) hclb1
  have hlip := cStar_lipschitzOn hl0 hl1 (by norm_num : (0 : ℝ) ≤ 1) le_rfl
  have hdiff : |cStar lam - cStar 1| ≤ 14 * (1 - lam) := by
    refine hlip.trans ?_
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
  have hnum : cStar 1 - cStar lam ≤ 14 * (1 - lam) :=
    le_trans (le_abs_self _) (by rwa [abs_sub_comm] at hdiff)
  unfold HD
  have heq : 2 - 1 / cStar 1 - (2 - 1 / cStar lam)
      = (cStar 1 - cStar lam) / (cStar lam * cStar 1) := by
    field_simp
    ring
  rw [heq, div_le_iff₀ (mul_pos hc0 hc1)]
  have hprod : 1 / (4 * Real.pi ^ 2) ≤ cStar lam * cStar 1 := by
    calc 1 / (4 * Real.pi ^ 2) = (1 / (2 * Real.pi)) * (1 / (2 * Real.pi)) := by field_simp; ring
      _ ≤ cStar lam * cStar 1 := mul_le_mul hclb hclb1 (by positivity) hc0.le
  calc cStar 1 - cStar lam ≤ 14 * (1 - lam) := hnum
    _ = (56 * Real.pi ^ 2 * (1 - lam)) * (1 / (4 * Real.pi ^ 2)) := by field_simp; ring
    _ ≤ (56 * Real.pi ^ 2 * (1 - lam)) * (cStar lam * cStar 1) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)

/-! ## Section 3. Eventual disjoint-pair Frobenius slack on `S₁` -/

/-- **Eventual disjoint-pair Schur–Jensen slack.**
For any `P` with `P.Valid` and `λ ∈ [999999/1000000, 1)`, eventually in `T` there exists a
pairwise-disjoint family of pairs in `(blockData Z T (P.atD T) hconj).S₁` whose finite-grid
squared overlaps sum to `2 · ∑ overlap² ≥ 10⁻⁸ · N(T, 2T)`. -/
theorem eventually_exists_disjointPairs_slack (Z : ZeroConfig) (H : PaperInputs Z)
    {P : Params} (hP : P.Valid)
    (hlam_lo : 999999 / 1000000 ≤ P.lam) (hlam : P.lam < 1) :
    ∀ᶠ T in atTop,
      ∀ (hconj : PhiHatConj T (P.atD T)),
      ∃ (r : Finset ℕ) (x y : ℕ → ZI Z T),
        (∀ p ∈ r, x p ∈ (blockData Z T (P.atD T) hconj).S₁) ∧
        (∀ p ∈ r, y p ∈ (blockData Z T (P.atD T) hconj).S₁) ∧
        (∀ p ∈ r, x p ≠ y p) ∧
        (r : Set ℕ).PairwiseDisjoint (fun p => ({x p, y p} : Finset (ZI Z T))) ∧
        (1 / 10 ^ 8 : ℝ) * (Z.N T (2 * T) : ℝ)
          ≤ 2 * ∑ p ∈ r, (pairGridOverlap Z (P.atD T) T (x p) (y p)) ^ 2 := by
  -- Step 1: Lower bound `HD(P.lam) ≥ 6718 / 10000`
  have hHD1 : (1681 / 2500 : ℝ) ≤ HD 1 := RHTower.HD_one_ge
  have hHD_lip := HD_one_sub_HD_le (by linarith : 1 / 2 ≤ P.lam) hlam.le
  have hpi_sq : Real.pi ^ 2 < 10 := by
    have hpi := Real.pi_lt_d4
    have h0 : 0 < Real.pi := Real.pi_pos
    nlinarith
  have hHD_lam : (6718 / 10000 : ℝ) ≤ HD P.lam := by
    have hsub : 1 - P.lam ≤ 1 / 1000000 := by linarith
    have h56 : 56 * Real.pi ^ 2 * (1 - P.lam) ≤ 56 * 10 * (1 / 1000000) := by nlinarith
    linarith
  -- Step 2: Baseline simple critical-line count from Zeta23's Theorem D at `ε = 1 / 10000`
  obtain ⟨T_base, hbase⟩ := (thmD_mult_lam_abstract Z H P hP hlam).1 (1 / 10000) (by norm_num)
  have hev_base : ∀ᶠ T in atTop, (6717 / 10000 : ℝ) * (Z.N T (2 * T) : ℝ) ≤ Z.N0s T (2 * T) := by
    filter_upwards [eventually_ge_atTop T_base] with T hT
    have h1 := hbase T hT
    have hN0 : (0 : ℝ) ≤ Z.N T (2 * T) := Nat.cast_nonneg _
    nlinarith
  -- Step 3: Boundary strip o(N), scale bound, N → ∞, and uniform finite-grid approximation
  have hev_bd := (isLittleO_boundary_N Z H.RvM).def (show (0 : ℝ) < 1 / 10000 by norm_num)
  have hev_scale := eventually_L_mul_T_div_two_pi_le_N Z H.RvM hP.lam_pos hlam
  have hev_Nbig := (tendsto_N_atTop Z H.RvM).eventually_ge_atTop (30000 : ℝ)
  have hev_grid := eventually_pairGridOverlap_atD_close Z hP
  filter_upwards [eventually_ge_atTop (16 : ℝ), eventually_l_pos, hev_base, hev_bd, hev_scale,
    hev_Nbig, hev_grid] with T hT16 hl hN0s hbd hscale hNbig hgrid
  intro hconj
  set N : ℝ := (Z.N T (2 * T) : ℝ)
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg hN0] at hbd
  -- Step 4: Lower bound on `#S₁Bulk`
  set SB := S₁Bulk Z P T hconj
  have hdecomp : (Z.N0s T (2 * T) : ℝ)
      ≤ (SB.card : ℝ) + ((Z.N T (T + Real.sqrt T) + Z.N (2 * T - Real.sqrt T) (2 * T) : ℕ) : ℝ) := by
    have h := N0s_le_card_S₁Bulk_add_boundary Z P (by linarith) hconj
    have hcast : ((SB.card + Z.N T (T + Real.sqrt T) + Z.N (2 * T - Real.sqrt T) (2 * T) : ℕ) : ℝ)
        = (SB.card : ℝ) + ((Z.N T (T + Real.sqrt T) + Z.N (2 * T - Real.sqrt T) (2 * T) : ℕ) : ℝ) := by
      push_cast; ring
    exact (Nat.cast_le.mpr h).trans_eq hcast
  have hSB_ge : (6716 / 10000 : ℝ) * N ≤ (SB.card : ℝ) := by linarith
  have hm3 : 3 ≤ SB.card := by
    have : (3 : ℝ) ≤ (SB.card : ℝ) := by linarith
    exact_mod_cast this
  have hm_sub2 : (6715 / 10000 : ℝ) * N ≤ ((SB.card - 2 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 2 ≤ SB.card)]
    push_cast
    linarith
  -- Step 5: Order `SB` strictly by imaginary part (injective on `onLine` where `Re = 1/2`)
  have him_injOn : Set.InjOn (fun z : ZI Z T => (z : ℂ).im) (SB : Set (ZI Z T)) := by
    intro z₁ hz₁ z₂ hz₂ him
    rw [Finset.mem_coe] at hz₁ hz₂
    have hS1_1 := (Finset.mem_filter.mp hz₁).1
    have hS1_2 := (Finset.mem_filter.mp hz₂).1
    have hre1 : (z₁ : ℂ).re = 1 / 2 := by
      have h := (Finset.mem_filter.mp hS1_1).2.1
      dsimp only [blockData] at h
      exact (mkData_σ_eq_iff Z T _ _ z₁).mp h
    have hre2 : (z₂ : ℂ).re = 1 / 2 := by
      have h := (Finset.mem_filter.mp hS1_2).2.1
      dsimp only [blockData] at h
      exact (mkData_σ_eq_iff Z T _ _ z₂).mp h
    apply Subtype.ext
    apply Complex.ext
    · rw [hre1, hre2]
    · exact him
  set Γ : Finset ℝ := SB.image (fun z : ZI Z T => (z : ℂ).im)
  have hΓ_card : Γ.card = SB.card := Finset.card_image_of_injOn him_injOn
  set m : ℕ := Γ.card
  have hm_ge3 : 3 ≤ m := hΓ_card ▸ hm3
  let e := Γ.orderEmbOfFin (rfl : Γ.card = m)
  set g : Fin m → ℝ := fun i => e i
  have hg_mono : StrictMono g := e.strictMono
  have hg_mem : ∀ i : Fin m, g i ∈ Γ := fun i => Γ.orderEmbOfFin_mem (rfl : Γ.card = m) i
  -- Lift each `g i ∈ Γ` back to its unique point `zOf i ∈ SB`
  let zOf : Fin m → ZI Z T := fun i => Classical.choose (Finset.mem_image.mp (hg_mem i))
  have hzOf_mem : ∀ i : Fin m, zOf i ∈ SB := fun i =>
    (Classical.choose_spec (Finset.mem_image.mp (hg_mem i))).1
  have hzOf_im : ∀ i : Fin m, (zOf i : ℂ).im = g i := fun i =>
    (Classical.choose_spec (Finset.mem_image.mp (hg_mem i))).2
  have hzOf_inj : Function.Injective zOf := by
    intro i₁ i₂ heq
    exact hg_mono.injective (by rw [← hzOf_im i₁, ← hzOf_im i₂, heq])
  have hzOf_S₁ : ∀ i : Fin m, zOf i ∈ (blockData Z T (P.atD T) hconj).S₁ := fun i =>
    (Finset.mem_filter.mp (hzOf_mem i)).1
  have hzOf_bulk : ∀ i : Fin m, T + Real.sqrt T ≤ (zOf i : ℂ).im ∧ (zOf i : ℂ).im ≤ 2 * T - Real.sqrt T := by
    intro i
    have hb := (Finset.mem_filter.mp (hzOf_mem i)).2
    exact ⟨hb.1.le, hb.2⟩
  have hg_bounds : ∀ i : Fin m, T + Real.sqrt T ≤ g i ∧ g i ≤ 2 * T - Real.sqrt T := fun i => by
    rw [← hzOf_im i]
    exact hzOf_bulk i
  -- Step 6: Apply `exists_disjoint_short_triples` at scale `α = P.L T / (2π)`
  set α : ℝ := P.L T / (2 * Real.pi)
  have hα_pos : 0 < α := by simp only [α, Params.L]; have := hP.lam_pos; positivity
  have hab : T + Real.sqrt T ≤ 2 * T - Real.sqrt T := by
    have h4 : 4 ≤ Real.sqrt T := by
      rw [show (4 : ℝ) = Real.sqrt 16 by norm_num]
      exact Real.sqrt_le_sqrt hT16
    have h2s : 2 * Real.sqrt T ≤ T := by
      have : (2 * Real.sqrt T) ^ 2 ≤ T ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by linarith)]; nlinarith
      nlinarith [sq_nonneg (T - 2 * Real.sqrt T)]
    linarith
  obtain ⟨R, hR_lt, hR_card, hR_span, hR_sep⟩ :=
    exists_disjoint_short_triples hm_ge3 hg_mono hab hα_pos hg_bounds
  -- Bound `R.card ≥ (1 / 625) * N`
  have hα_span_le : α * ((2 * T - Real.sqrt T) - (T + Real.sqrt T)) ≤ N := by
    have hlen : (2 * T - Real.sqrt T) - (T + Real.sqrt T) ≤ T := by linarith [Real.sqrt_nonneg T]
    calc α * ((2 * T - Real.sqrt T) - (T + Real.sqrt T))
        ≤ α * T := mul_le_mul_of_nonneg_left hlen hα_pos.le
      _ = P.L T * T / (2 * Real.pi) := by simp only [α]; ring
      _ ≤ N := hscale
  have hR_card_ge : (1 / 625 : ℝ) * N ≤ (R.card : ℝ) := by
    have hm_eq : ((m - 2 : ℕ) : ℝ) = ((SB.card - 2 : ℕ) : ℝ) := by rw [show m = SB.card from hΓ_card]
    rw [hm_eq] at hR_card
    linarith
  -- Step 7: In each short triple `j ∈ R`, select a pair with `|mtKernel| ≥ 1 / 250`
  have hex_pair : ∀ (j : ℕ) (hj : j ∈ R),
      ∃ u v : ZI Z T,
        u ∈ ({zOf ⟨j, by have := hR_lt j hj; omega⟩,
              zOf ⟨j + 1, by have := hR_lt j hj; omega⟩,
              zOf ⟨j + 2, hR_lt j hj⟩} : Finset (ZI Z T)) ∧
        v ∈ ({zOf ⟨j, by have := hR_lt j hj; omega⟩,
              zOf ⟨j + 1, by have := hR_lt j hj; omega⟩,
              zOf ⟨j + 2, hR_lt j hj⟩} : Finset (ZI Z T)) ∧
        u ≠ v ∧
        1 / 250 ≤ |mtKernel P.lam (α * |(u : ℂ).im - (v : ℂ).im|)| := by
    intro j hj
    have h2 : j + 2 < m := hR_lt j hj
    have h1 : j + 1 < m := by omega
    have h0 : j < m := by omega
    have h12 : (zOf ⟨j, h0⟩ : ℂ).im < (zOf ⟨j + 1, h1⟩ : ℂ).im := by
      rw [hzOf_im, hzOf_im]
      exact hg_mono (Fin.mk_lt_mk.mpr (by omega))
    have h23 : (zOf ⟨j + 1, h1⟩ : ℂ).im < (zOf ⟨j + 2, h2⟩ : ℂ).im := by
      rw [hzOf_im, hzOf_im]
      exact hg_mono (Fin.mk_lt_mk.mpr (by omega))
    have hsp : α * ((zOf ⟨j + 2, h2⟩ : ℂ).im - (zOf ⟨j, h0⟩ : ℂ).im) ≤ 3 := by
      rw [hzOf_im, hzOf_im]
      exact hR_span j hj
    exact exists_pair_in_triple_mtKernel_ge (by linarith : 999 / 1000 ≤ P.lam) hlam.le hα_pos
      (fun z : ZI Z T => (z : ℂ).im) h12 h23 hsp
  classical
  let x : ℕ → ZI Z T := fun j =>
    if hj : j ∈ R then Classical.choose (hex_pair j hj) else zOf ⟨0, by omega⟩
  let y : ℕ → ZI Z T := fun j =>
    if hj : j ∈ R then Classical.choose (Classical.choose_spec (hex_pair j hj))
    else zOf ⟨1, by omega⟩
  have hxy_spec : ∀ j (hj : j ∈ R),
      let T_j : Finset (ZI Z T) :=
        {zOf ⟨j, by have := hR_lt j hj; omega⟩,
         zOf ⟨j + 1, by have := hR_lt j hj; omega⟩,
         zOf ⟨j + 2, hR_lt j hj⟩}
      x j ∈ T_j ∧ y j ∈ T_j ∧ x j ≠ y j ∧
        1 / 250 ≤ |mtKernel P.lam (α * |(x j : ℂ).im - (y j : ℂ).im|)| := by
    intro j hj
    simp only [x, y, dif_pos hj]
    exact Classical.choose_spec (Classical.choose_spec (hex_pair j hj))
  have hx_SB : ∀ j ∈ R, x j ∈ SB := by
    intro j hj
    have hmem := (hxy_spec j hj).1
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h <;> (rw [h]; exact hzOf_mem _)
  have hy_SB : ∀ j ∈ R, y j ∈ SB := by
    intro j hj
    have hmem := (hxy_spec j hj).2.1
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h <;> (rw [h]; exact hzOf_mem _)
  refine ⟨R, x, y, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj; exact (Finset.mem_filter.mp (hx_SB j hj)).1
  · intro j hj; exact (Finset.mem_filter.mp (hy_SB j hj)).1
  · intro j hj; exact (hxy_spec j hj).2.2.1
  · -- Pairwise disjointness across `j ∈ R` from `3`-separation and `hzOf_inj`
    intro j₁ hj₁ j₂ hj₂ hne
    rw [Finset.mem_coe] at hj₁ hj₂
    have hsep := hR_sep j₁ hj₁ j₂ hj₂ hne
    set T₁ : Finset (ZI Z T) :=
      {zOf ⟨j₁, by have := hR_lt j₁ hj₁; omega⟩,
       zOf ⟨j₁ + 1, by have := hR_lt j₁ hj₁; omega⟩,
       zOf ⟨j₁ + 2, hR_lt j₁ hj₁⟩}
    set T₂ : Finset (ZI Z T) :=
      {zOf ⟨j₂, by have := hR_lt j₂ hj₂; omega⟩,
       zOf ⟨j₂ + 1, by have := hR_lt j₂ hj₂; omega⟩,
       zOf ⟨j₂ + 2, hR_lt j₂ hj₂⟩}
    have hsub₁ : ({x j₁, y j₁} : Finset (ZI Z T)) ⊆ T₁ := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact (hxy_spec j₁ hj₁).1
      · exact (hxy_spec j₁ hj₁).2.1
    have hsub₂ : ({x j₂, y j₂} : Finset (ZI Z T)) ⊆ T₂ := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact (hxy_spec j₂ hj₂).1
      · exact (hxy_spec j₂ hj₂).2.1
    refine Disjoint.mono hsub₁ hsub₂ ?_
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    simp only [T₁, T₂, Finset.mem_insert, Finset.mem_singleton] at hz1 hz2
    rcases hz1 with rfl | rfl | rfl <;> rcases hz2 with heq | heq | heq
    all_goals
      have hidx := Fin.mk.inj_iff.mp (hzOf_inj heq)
      omega
  · -- Lower bound on `2 * ∑_{j ∈ R} pairGridOverlap^2`
    have hpt_sq : ∀ j ∈ R, (1 / 250000 : ℝ) ≤ (pairGridOverlap Z (P.atD T) T (x j) (y j)) ^ 2 := by
      intro j hj
      have hx_b := (Finset.mem_filter.mp (hx_SB j hj)).2
      have hy_b := (Finset.mem_filter.mp (hy_SB j hj)).2
      have hclose := hgrid (x j) (y j) hx_b.1.le hx_b.2 hy_b.1.le hy_b.2
      have hK_ge := (hxy_spec j hj).2.2.2
      have habs_ge : 1 / 500 ≤ |pairGridOverlap Z (P.atD T) T (x j) (y j)| := by
        have htri := abs_sub_abs_le_abs_sub
          (mtKernel P.lam (α * |(x j : ℂ).im - (y j : ℂ).im|))
          (pairGridOverlap Z (P.atD T) T (x j) (y j))
        rw [abs_sub_comm (mtKernel P.lam (α * |(x j : ℂ).im - (y j : ℂ).im|))] at htri
        linarith
      have hsq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 500) habs_ge 2
      rw [sq_abs] at hsq
      norm_num at hsq ⊢
      exact hsq
    have hsum_ge : (R.card : ℝ) * (1 / 250000)
        ≤ ∑ p ∈ R, (pairGridOverlap Z (P.atD T) T (x p) (y p)) ^ 2 := by
      calc (R.card : ℝ) * (1 / 250000) = ∑ _ ∈ R, (1 / 250000 : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ p ∈ R, (pairGridOverlap Z (P.atD T) T (x p) (y p)) ^ 2 :=
            Finset.sum_le_sum hpt_sq
    nlinarith

/-! ## Section 4. Abstract `c = 3` seam consumer and fixed-`λ` theorems -/

/-- **Theorem D (`c = 3`) from an abstract seam.**
Any function `Cnt3 : ℝ → ℝ` such that `2 * Cnt3 T` eventually dominates the unmodified `c = 3`
multiplicity-aware seam satisfies `(3/2 − c⁻¹/2 − ε) · N(T, 2T) ≤ Cnt3 T` eventually. -/
theorem thmD_mult3_count_of_seam (Z : ZeroConfig) (H : PaperInputs Z) (P : Params) (hP : P.Valid)
    (hlam : P.lam < 1)
    (aT bT JT trG trG2 : ℝ → ℝ)
    (hTr : TracesBoundsD P aT bT JT trG trG2 (fun T => (Z.N T (2 * T) : ℝ)))
    {c : ℝ} (hc0 : 0 < c)
    (hc : Tendsto (fun T => cRatio (P.lam1 T) (aT T) (bT T) (JT T)) atTop (𝓝 c))
    (ha : ∀ᶠ T in atTop, 1 / 2 ≤ aT T ∧ aT T ≤ 1)
    (θ₀ : ℝ → ℝ) (hTail : ∀ᶠ T in atTop, TailInputs Z (P.atD T) T (θ₀ T))
    (hθ₀ : ∃ C : ℝ, ∀ᶠ T in atTop, θ₀ T ≤ C * l T * T ^ (P.lam / 2 - 1))
    (hNII : ∃ C : ℝ, ∀ᶠ T in atTop, (NII Z T : ℝ) ≤ C * Real.sqrt T * l T)
    (hGzGp : ∀ᶠ T in atTop, Z.Gz (P.atD T) T = (P.atD T).Gp T)
    (hId : ∀ᶠ T in atTop, (P.atD T).trGtilde T = trG T ∧ (P.atD T).trGtildeSq T = trG2 T ∧
      (P.atD T).a T = aT T)
    (hcalE : Tendsto P.calE atTop (𝓝 0)) (Cnt3 : ℝ → ℝ)
    (hseam : ∀ᶠ T in atTop,
      6 * RHLinalg.rtrace ((P.atD T).hat T (Z.Gz (P.atD T) T))
        - RHLinalg.frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T))
        - 3 * (Z.N T (2 * T) : ℝ) - 5 * (NII Z T : ℝ)
        - θ₀ T / ((P.atD T).a T * (P.atD T).L T)
          * (6 + 2 * Real.sqrt (RHLinalg.frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T)))
            + θ₀ T / ((P.atD T).a T * (P.atD T).L T))
        ≤ 2 * Cnt3 T) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (3 / 2 - c⁻¹ / 2 - ε) * (Z.N T (2 * T) : ℝ) ≤ Cnt3 T := by
  intro ε hε
  have hlam0 := hP.lam_pos
  have hlam1 : P.lam ≤ 1 := hlam.le
  obtain ⟨C₁, hC₁, T₁, htr1⟩ := hTr.tr1
  obtain ⟨C₂, hC₂, T₂, hfr2⟩ := hTr.frhat
  obtain ⟨Cθ, hθ⟩ := hθ₀
  obtain ⟨CII, hII⟩ := hNII
  set N : ℝ → ℝ := fun T => (Z.N T (2 * T) : ℝ) with hNdef
  set cinv : ℝ → ℝ := fun T => (cRatio (P.lam1 T) (aT T) (bT T) (JT T))⁻¹ with hcinv
  set R₁ : ℝ → ℝ := fun T => C₁ * Real.sqrt (P.X T) / aT T with hR₁
  set R₂ : ℝ → ℝ := fun T => C₂ * P.calE T * (cinv T * N T) with hR₂
  set B : ℝ → ℝ := fun T => θ₀ T / (aT T * P.L T) with hBdef
  set err : ℝ → ℝ := fun T => (6 * R₁ T + R₂ T + 5 * (NII Z T : ℝ)
      + B T * (6 + 2 * Real.sqrt (cinv T * N T + R₂ T) + B T)) + |cinv T - c⁻¹| * N T with herr
  have hcinv_to : Tendsto cinv atTop (𝓝 c⁻¹) := hc.inv₀ hc0.ne'
  have hmain : ∀ᶠ T in atTop, (3 - c⁻¹) * N T - err T ≤ 2 * Cnt3 T := by
    filter_upwards [hseam, hTail, hGzGp, hId, ha, eventually_ge_atTop T₁,
      eventually_ge_atTop T₂, eventually_l_pos]
      with T hA hTl hGG hid ha2 hT₁ hT₂ hl
    obtain ⟨hidtr, hidfr, hida⟩ := hid
    have hapos' : 0 < aT T := by linarith [ha2.1]
    have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
    have hrt : RHLinalg.rtrace ((P.atD T).hat T (Z.Gz (P.atD T) T)) = (aT T * P.L T)⁻¹ * trG T := by
      rw [rtrace_hat, hGG, rtrace_tilde_Gp, hidtr, hida]; rfl
    have hfr : RHLinalg.frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T))
        = ((aT T * P.L T)⁻¹) ^ 2 * trG2 T := by
      rw [frobSq_hat, hGG, frobSq_tilde_Gp, hidfr, hida]; rfl
    have haL : (P.atD T).a T * (P.atD T).L T = aT T * P.L T := by rw [hida]; rfl
    rw [hrt, hfr, haL] at hA
    have htr : |(aT T * P.L T)⁻¹ * trG T - N T| ≤ R₁ T :=
      trGhat_sub_N_le hapos' hLpos (by simpa only using htr1 T hT₁)
    have hfrb : ((aT T * P.L T)⁻¹) ^ 2 * trG2 T ≤ cinv T * N T + R₂ T := by
      have h := hfr2 T hT₂
      simp only at h
      have h1 : trG2 T / (aT T * P.L T) ^ 2 - cinv T * N T ≤ C₂ * P.calE T * (cinv T * N T) := by
        rw [← mul_assoc] at h
        exact le_trans (le_trans (le_max_left _ 0) (le_abs_self _)) h
      have e : ((aT T * P.L T)⁻¹) ^ 2 * trG2 T = trG2 T / (aT T * P.L T) ^ 2 := by
        rw [inv_pow, div_eq_inv_mul]
      rw [e]; simp only [hR₂]; linarith
    have hB₀ : 0 ≤ B T := div_nonneg hTl.theta_nonneg (mul_pos hapos' hLpos).le
    have h := Nd_lower_c3 hB₀ hA htr hfrb
    have hN0 : 0 ≤ N T := Nat.cast_nonneg _
    have hcd : (3 - c⁻¹) * N T - |cinv T - c⁻¹| * N T ≤ (3 - cinv T) * N T := by
      have h1 := mul_le_mul_of_nonneg_right (le_abs_self (cinv T - c⁻¹)) hN0
      linarith [h1]
    simp only [herr, hR₁, hR₂, hBdef, hNdef] at h hcd ⊢
    linarith
  have hNtop : Tendsto N atTop atTop := tendsto_N_atTop Z H.RvM
  have o1 : R₁ =o[atTop] N := by
    have hbd : (fun T => C₁ / aT T) =O[atTop] (fun _ => (1 : ℝ)) := by
      refine isBigO_one_of_abs_le (C := 2 * C₁) ?_
      filter_upwards [ha] with T ha2
      rw [abs_of_nonneg (div_nonneg hC₁.le (by linarith [ha2.1]))]
      rw [div_le_iff₀ (by linarith [ha2.1])]; nlinarith [ha2.1]
    have := isLittleO_of_bdd_mul hbd
      (isLittleO_N_of_isLittleO_Tl Z H.RvM (isLittleO_sqrtX_Tl P hlam0 hlam1))
    exact this.congr_left fun T => by simp only [hR₁]; ring
  have hcinv_bd : ∀ᶠ T in atTop, 0 ≤ cinv T ∧ cinv T ≤ 2 * c⁻¹ := by
    have hcpos : (0 : ℝ) < c⁻¹ := inv_pos.mpr hc0
    filter_upwards [hcinv_to.eventually (eventually_ge_nhds hcpos),
      hcinv_to.eventually (eventually_le_nhds (show c⁻¹ < 2 * c⁻¹ by linarith))] with T h1 h2
    exact ⟨h1, h2⟩
  have hcinvO : cinv =O[atTop] (fun _ => (1 : ℝ)) := by
    refine isBigO_one_of_abs_le (C := 2 * c⁻¹) ?_
    filter_upwards [hcinv_bd] with T h
    rw [abs_of_nonneg h.1]; exact h.2
  have o2 : R₂ =o[atTop] N := by
    have hcE0 : Tendsto (fun T => C₂ * P.calE T) atTop (𝓝 0) := by
      simpa using hcalE.const_mul C₂
    have i1 : (fun T => cinv T * N T) =O[atTop] N := by
      have := hcinvO.mul (isBigO_refl N atTop)
      simpa using this
    have := ((isLittleO_one_iff ℝ).2 hcE0).mul_isBigO i1
    refine (this.congr_left fun T => ?_).congr_right fun T => by simp
    simp only [hR₂]
  have o3 : (fun T => (NII Z T : ℝ)) =o[atTop] N := by
    have hO : (fun T => (NII Z T : ℝ)) =O[atTop] (fun T => Real.sqrt T * l T) := by
      refine IsBigO.of_bound CII ?_
      filter_upwards [hII, eventually_l_pos] with T h hl
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
        abs_of_nonneg (by positivity)]
      simpa [mul_assoc] using h
    exact hO.trans_isLittleO (isLittleO_N_of_isLittleO_Tl Z H.RvM isLittleO_sqrt_mul_l_Tl)
  have o4 : Tendsto B atTop (𝓝 0) := by
    have hup : Tendsto (fun T => 2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) atTop (𝓝 0) := by
      simpa using (tendsto_theta_over_L P hlam0 hlam1).const_mul (2 * |Cθ|)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [hTail, ha, eventually_l_pos] with T hTl ha2 hl
      have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
      exact div_nonneg hTl.theta_nonneg (by nlinarith [ha2.1])
    · filter_upwards [hTail, ha, eventually_l_pos, hθ, eventually_gt_atTop (0 : ℝ)]
        with T hTl ha2 hl hθT hT0
      have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
      have hapos' : 0 < aT T := by linarith [ha2.1]
      simp only [hBdef]
      rw [div_le_iff₀ (mul_pos hapos' hLpos)]
      calc θ₀ T ≤ Cθ * l T * T ^ (P.lam / 2 - 1) := hθT
        _ ≤ |Cθ| * l T * T ^ (P.lam / 2 - 1) := by gcongr; exact le_abs_self _
        _ = |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T) * P.L T := by field_simp
        _ ≤ (2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) * (aT T * P.L T) := by
            have : |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T) * P.L T
                = (2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) * (1 / 2 * P.L T) := by ring
            rw [this]; gcongr; exact ha2.1
  have o5 := err_isLittleO (R₁ := R₁) (R₂ := R₂) (NII := fun T => (NII Z T : ℝ)) (B := B)
    (cl := cinv) hNtop o1 o2 o3 o4 hcinv_bd
  have o6 : (fun T => |cinv T - c⁻¹| * N T) =o[atTop] N := by
    refine isLittleO_of_tendsto_zero_mul ?_
    have : Tendsto (fun T => cinv T - c⁻¹) atTop (𝓝 0) := by
      simpa using hcinv_to.sub_const c⁻¹
    simpa using this.abs
  have oB : B =o[atTop] N := by
    refine ((isLittleO_one_iff ℝ).2 o4).trans_isBigO (IsBigO.of_bound 1 ?_)
    filter_upwards [hNtop.eventually_ge_atTop 1] with T h1
    rw [norm_one, Real.norm_eq_abs, abs_of_nonneg (by linarith), one_mul]; exact h1
  have o5' : (fun T => 6 * R₁ T + R₂ T + 5 * (NII Z T : ℝ)
      + B T * (6 + 2 * Real.sqrt (cinv T * N T + R₂ T) + B T)) =o[atTop] N := by
    have := o5.add (((o1.const_mul_left 2).add (o3.const_mul_left 2)).add (oB.const_mul_left 2))
    exact this.congr_left fun T => by ring
  have herr_o : err =o[atTop] N := o5'.add o6
  obtain ⟨T₀, hT₀⟩ := eps_form_of_isLittleO hmain
    (Eventually.of_forall fun T => Nat.cast_nonneg _) herr_o (2 * ε) (by linarith)
  exact ⟨T₀, fun T hT => by have := hT₀ T hT; linarith⟩

/-- **Abstract fixed-`λ` improvement over Theorem D.**
For any `P` with `P.Valid` and `P.lam ∈ [999999/1000000, 1)`, the simple critical-line proportion
exceeds `HD(P.lam)` by `10⁻⁸` and the distinct-zero proportion exceeds `GD(P.lam)` by `(1/2) · 10⁻⁸`. -/
theorem thmD_beyond_lam_abstract (Z : ZeroConfig) (H : PaperInputs Z) (P : Params) (hP : P.Valid)
    (hlam_lo : 999999 / 1000000 ≤ P.lam) (hlam : P.lam < 1) :
    (∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (HD P.lam + 1 / 10 ^ 8 - ε) * (Z.N T (2 * T) : ℝ) ≤ Z.N0s T (2 * T)) ∧
    (∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (GD P.lam + 1 / (2 * 10 ^ 8) - ε) * (Z.N T (2 * T) : ℝ) ≤ Z.Nd T (2 * T)) := by
  have hLoc : LocalHypsCoreDEventually P := localHypsCoreD_eventually hP
  have hTr := tracesBoundsD_concrete (Z := Z) hP H hLoc
  have hc := tendsto_cRatio_concrete hP Z
  have hc0 := cStar_pos hP.lam_pos hP.lam_le_one
  have ha : ∀ᶠ T in atTop, 1 / 2 ≤ (concreteDataD P Z).aT T ∧ (concreteDataD P Z).aT T ≤ 1 :=
    (concreteFactsD hP H hLoc).ab_range.mono fun T h => ⟨h.1.trans h.2.1, h.2.2.1⟩
  obtain ⟨θ₀, hTail, hθ₀⟩ := eventually_tailPackageD Z H hP
  obtain ⟨A₀, hA₀, hloc⟩ := H.RvM.local_count
  have hNII := Tail.eventually_NII_le Z hA₀ hloc
  have hGzGp := eventually_GzGpD Z H hP
  have hId : ∀ᶠ T in atTop,
      (P.atD T).trGtilde T = (concreteDataD P Z).trG T ∧
      (P.atD T).trGtildeSq T = (concreteDataD P Z).trG2 T ∧
      (P.atD T).a T = (concreteDataD P Z).aT T :=
    Eventually.of_forall fun T =>
      ⟨Params.atD_trGtilde T hP, Params.atD_trGtildeSq T hP, Params.atD_a T hP⟩
  have hcalE := calE_tendsto_zero P hP.lam_pos hP.lam_le_one (zero_le_one.trans hP.one_le_w)
  have hslack := eventually_exists_disjointPairs_slack Z H hP hlam_lo hlam
  refine ⟨?_, ?_⟩
  · -- `c = 2`: feed `Cnt(T) := N0s(T, 2T) − 10⁻⁸ · N(T, 2T)` into `RHTower.thmD_count_of_seam`
    have hcnt := RHTower.thmD_count_of_seam Z H P hP hlam _ _ _ _ _ hTr hc0 hc ha θ₀ hTail hθ₀ hNII
      hGzGp hId hcalE (fun T => (Z.N0s T (2 * T) : ℝ) - (1 / 10 ^ 8 : ℝ) * (Z.N T (2 * T) : ℝ)) ?_
    · intro ε hε
      obtain ⟨T₀, hT₀⟩ := hcnt ε hε
      refine ⟨T₀, fun T hT => ?_⟩
      have h := hT₀ T hT
      simp only [HD, one_div] at h ⊢
      linarith
    · filter_upwards [hTail, hId, ha, eventually_ge_atTop (0 : ℝ), eventually_l_pos,
        eventually_w8 hP, hslack] with T hTl hid ha2 hT0 hl h8 hsT
      have haposD : 0 < (P.atD T).a T := by rw [hid.2.2]; linarith [ha2.1]
      have hLpos : 0 < (P.atD T).L T := by rw [Params.atD_L]; simp only [Params.L]; have := hP.lam_pos; positivity
      obtain ⟨r, x, y, hxS₁, hyS₁, hne, hdisj, hsum⟩ :=
        hsT (fun z => GzGp.phiHat_conj _ T z)
      have hseam := seamA_mult2_disjointPairs hT0 (fun z => GzGp.phiHat_conj _ T z)
        (fun s => GzGp.phiHat_ofReal _ T s) (poissonSqD hP h8) hTl haposD hLpos
        r x y hxS₁ hyS₁ hne hdisj
      linarith
  · -- `c = 3`: feed `Cnt3(T) := Nd(T, 2T) − (1/(2·10⁸)) · N(T, 2T)` into `thmD_mult3_count_of_seam`
    have hcnt := thmD_mult3_count_of_seam Z H P hP hlam _ _ _ _ _ hTr hc0 hc ha θ₀ hTail hθ₀ hNII
      hGzGp hId hcalE
      (fun T => (Z.Nd T (2 * T) : ℝ) - (1 / (2 * 10 ^ 8) : ℝ) * (Z.N T (2 * T) : ℝ)) ?_
    · intro ε hε
      obtain ⟨T₀, hT₀⟩ := hcnt ε hε
      refine ⟨T₀, fun T hT => ?_⟩
      have h := hT₀ T hT
      simp only [GD] at h ⊢
      linarith
    · filter_upwards [hTail, hId, ha, eventually_ge_atTop (0 : ℝ), eventually_l_pos,
        eventually_w8 hP, hslack] with T hTl hid ha2 hT0 hl h8 hsT
      have haposD : 0 < (P.atD T).a T := by rw [hid.2.2]; linarith [ha2.1]
      have hLpos : 0 < (P.atD T).L T := by rw [Params.atD_L]; simp only [Params.L]; have := hP.lam_pos; positivity
      obtain ⟨r, x, y, hxS₁, hyS₁, hne, hdisj, hsum⟩ :=
        hsT (fun z => GzGp.phiHat_conj _ T z)
      have hseam := seamA_mult3_disjointPairs hT0 (fun z => GzGp.phiHat_conj _ T z)
        (fun s => GzGp.phiHat_ofReal _ T s) (poissonSqD hP h8) hTl haposD hLpos
        r x y hxS₁ hyS₁ hne hdisj
      linarith

/-! ## Section 5. Unconditional flagship theorems for `ζ(s)` and `ξ(s)` -/

/-- **Dyadic simple critical-line zero proportion strictly beyond `HD(1)` (`ζ(s)`, unconditional).**
For every `ε > 0` and all sufficiently large `T`,
`(HD(1) + 10⁻⁸ − ε) · N(T, 2T) ≤ N₀ˢ(T, 2T)`. -/
theorem beyond_HD_one_simple_critical_dyadic :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Zeta23.ThmD.HD 1 + 1 / 10 ^ 8 - ε) * (Zeta23.Ncount T (2 * T) : ℝ)
        ≤ Zeta23.N0simple T (2 * T) := by
  intro ε hε
  set lam : ℝ := max (999999 / 1000000) (1 - (ε / 2) / (56 * Real.pi ^ 2))
  have hlam_lo : 999999 / 1000000 ≤ lam := le_max_left _ _
  have hlam_pos : 0 < lam := by linarith
  have hlam_lt : lam < 1 := by
    apply max_lt (by norm_num)
    have : 0 < (ε / 2) / (56 * Real.pi ^ 2) := by positivity
    linarith
  have hsub : 1 - lam ≤ (ε / 2) / (56 * Real.pi ^ 2) := by
    have := le_max_right (999999 / 1000000 : ℝ) (1 - (ε / 2) / (56 * Real.pi ^ 2))
    linarith
  have hHD_gap : HD 1 - HD lam ≤ ε / 2 := by
    calc HD 1 - HD lam ≤ 56 * Real.pi ^ 2 * (1 - lam) :=
          HD_one_sub_HD_le (by linarith) hlam_lt.le
      _ ≤ 56 * Real.pi ^ 2 * ((ε / 2) / (56 * Real.pi ^ 2)) :=
          mul_le_mul_of_nonneg_left hsub (by positivity)
      _ = ε / 2 := by field_simp
  have hP := paramsOf_valid taperProfile_stdProfile hlam_pos hlam_lt.le
  obtain ⟨T₀, hT₀⟩ := (thmD_beyond_lam_abstract zetaZeroConfig paperInputs_zeta
    (paramsOf stdProfile lam) hP hlam_lo hlam_lt).1 (ε / 2) (by linarith)
  refine ⟨T₀, fun T hT => ?_⟩
  have h := hT₀ T hT
  simp only [paramsOf, zetaZeroConfig_N, zetaZeroConfig_N0s] at h
  have hN0 : (0 : ℝ) ≤ Zeta23.Ncount T (2 * T) := Nat.cast_nonneg _
  nlinarith

/-- **Cumulative simple critical-line zero proportion strictly beyond `HD(1)` (`ζ(s)`, unconditional).**
For every `ε > 0` and all sufficiently large `T`,
`(HD(1) + 10⁻⁸ − ε) · N(0, T) ≤ N₀ˢ(0, T)`. -/
theorem beyond_HD_one_simple_critical_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Zeta23.ThmD.HD 1 + 1 / 10 ^ 8 - ε) * (Zeta23.Ncount 0 T : ℝ)
        ≤ Zeta23.N0simple 0 T :=
  Zeta23.cumulative_of_dyadic Zeta23.zetaSeam Zeta23.paperInputs_zeta.RvM
    (fun _ _ _ => Zeta23.N0simple_add' Zeta23.zetaSeam)
    beyond_HD_one_simple_critical_dyadic

/-- **Dyadic critical-line zero proportion (with and without multiplicity) strictly beyond `HD(1)`.** -/
theorem beyond_HD_one_critical_dyadic :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Zeta23.ThmD.HD 1 + 1 / 10 ^ 8 - ε) * (Zeta23.Ncount T (2 * T) : ℝ)
        ≤ Zeta23.N0star T (2 * T) ∧
      (Zeta23.ThmD.HD 1 + 1 / 10 ^ 8 - ε) * (Zeta23.Ncount T (2 * T) : ℝ)
        ≤ Zeta23.N0 T (2 * T) ∧
      (Zeta23.ThmD.HD 1 + 1 / 10 ^ 8 - ε) * (Zeta23.Ncount T (2 * T) : ℝ)
        ≤ Zeta23.Nsimple T (2 * T) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := beyond_HD_one_simple_critical_dyadic ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  have h := hT₀ T hT
  have tc := Zeta23.trivial_chain Zeta23.zetaSeam T (2 * T)
  exact ⟨h.trans (Nat.cast_le.mpr tc.1),
    h.trans (Nat.cast_le.mpr (tc.1.trans tc.2.1)),
    h.trans (Nat.cast_le.mpr tc.2.2.2.1)⟩

/-- **Cumulative critical-line zero proportion (with and without multiplicity) strictly beyond `HD(1)`.** -/
theorem beyond_HD_one_critical_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Zeta23.ThmD.HD 1 + 1 / 10 ^ 8 - ε) * (Zeta23.Ncount 0 T : ℝ)
        ≤ Zeta23.N0star 0 T ∧
      (Zeta23.ThmD.HD 1 + 1 / 10 ^ 8 - ε) * (Zeta23.Ncount 0 T : ℝ)
        ≤ Zeta23.N0 0 T ∧
      (Zeta23.ThmD.HD 1 + 1 / 10 ^ 8 - ε) * (Zeta23.Ncount 0 T : ℝ)
        ≤ Zeta23.Nsimple 0 T := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := beyond_HD_one_simple_critical_cumulative ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  have h := hT₀ T hT
  have tc := Zeta23.trivial_chain Zeta23.zetaSeam 0 T
  exact ⟨h.trans (Nat.cast_le.mpr tc.1),
    h.trans (Nat.cast_le.mpr (tc.1.trans tc.2.1)),
    h.trans (Nat.cast_le.mpr tc.2.2.2.1)⟩

/-- **Dyadic distinct-zero proportion strictly beyond `GD(1)` (`ζ(s)`, unconditional).** -/
theorem beyond_GD_one_distinct_dyadic :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Zeta23.ThmD.GD 1 + 1 / (2 * 10 ^ 8) - ε) * (Zeta23.Ncount T (2 * T) : ℝ)
        ≤ Zeta23.Ndist T (2 * T) := by
  intro ε hε
  set lam : ℝ := max (999999 / 1000000) (1 - ε / (56 * Real.pi ^ 2))
  have hlam_lo : 999999 / 1000000 ≤ lam := le_max_left _ _
  have hlam_pos : 0 < lam := by linarith
  have hlam_lt : lam < 1 := by
    apply max_lt (by norm_num)
    have : 0 < ε / (56 * Real.pi ^ 2) := by positivity
    linarith
  have hsub : 1 - lam ≤ ε / (56 * Real.pi ^ 2) := by
    have := le_max_right (999999 / 1000000 : ℝ) (1 - ε / (56 * Real.pi ^ 2))
    linarith
  have hGD_gap : GD 1 - GD lam ≤ ε / 2 := by
    rw [GD_eq 1, GD_eq lam]
    have hHD : HD 1 - HD lam ≤ ε := by
      calc HD 1 - HD lam ≤ 56 * Real.pi ^ 2 * (1 - lam) :=
            HD_one_sub_HD_le (by linarith) hlam_lt.le
        _ ≤ 56 * Real.pi ^ 2 * (ε / (56 * Real.pi ^ 2)) :=
            mul_le_mul_of_nonneg_left hsub (by positivity)
        _ = ε := by field_simp
    linarith
  have hP := paramsOf_valid taperProfile_stdProfile hlam_pos hlam_lt.le
  obtain ⟨T₀, hT₀⟩ := (thmD_beyond_lam_abstract zetaZeroConfig paperInputs_zeta
    (paramsOf stdProfile lam) hP hlam_lo hlam_lt).2 (ε / 2) (by linarith)
  refine ⟨T₀, fun T hT => ?_⟩
  have h := hT₀ T hT
  simp only [paramsOf, zetaZeroConfig_N, zetaZeroConfig_Nd] at h
  have hN0 : (0 : ℝ) ≤ Zeta23.Ncount T (2 * T) := Nat.cast_nonneg _
  nlinarith

/-- **Cumulative distinct-zero proportion strictly beyond `GD(1)` (`ζ(s)`, unconditional).** -/
theorem beyond_GD_one_distinct_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Zeta23.ThmD.GD 1 + 1 / (2 * 10 ^ 8) - ε) * (Zeta23.Ncount 0 T : ℝ)
        ≤ Zeta23.Ndist 0 T :=
  Zeta23.cumulative_of_dyadic Zeta23.zetaSeam Zeta23.paperInputs_zeta.RvM
    (fun _ _ _ => Zeta23.Ndist_add' Zeta23.zetaSeam)
    beyond_GD_one_distinct_dyadic

/-- Eight-decimal rational enclosure `0.67250070 ≤ HD(1)` via degree-20 Taylor enclosures at `2^{-1/2}`. -/
theorem HD_one_ge_67250070 : (67250070 / 100000000 : ℝ) ≤ Zeta23.ThmD.HD 1 := by
  rw [Zeta23.ThmD.HD_one]
  set s : ℝ := (Real.sqrt 2)⁻¹ with hs
  have hsqrt0 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < s := inv_pos.mpr hsqrt0
  have hs2 : s ^ 2 = 1 / 2 := by rw [hs, inv_pow, hsq, one_div]
  have hsqrt_le : Real.sqrt 2 ≤ 71 / 50 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hs7 : 7 / 10 ≤ s := by
    rw [hs, le_inv_comm₀ (by norm_num) hsqrt0]; linarith
  have hs1 : s < 1 := by nlinarith
  have hsabs : |s| ≤ 10 := by rw [abs_of_pos hs0]; linarith
  set C : ℝ := ∑ j ∈ Finset.range 10, (-1 : ℝ) ^ j * (1 / 2) ^ j / ((2 * j).factorial : ℝ) with hC
  set S : ℝ := ∑ j ∈ Finset.range 10, (-1 : ℝ) ^ j * (1 / 2) ^ j
    / ((2 * j + 1).factorial : ℝ) with hS
  set r : ℝ := |s| ^ 20 / (Nat.factorial 20 : ℝ) * 2 with hr
  have hr_eq : r = (1 / 2) ^ 10 / (Nat.factorial 20 : ℝ) * 2 := by
    rw [hr, abs_of_pos hs0, show (20 : ℕ) = 2 * 10 by norm_num, pow_mul, hs2]
  have hr_small : r ≤ 1 / 10 ^ 20 := by
    rw [hr_eq]; norm_num [Nat.factorial]
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hcos := Encl.le_of_holds (encl_cos s hsabs)
  have hsin := Encl.ge_of_holds (encl_sin s hsabs)
  simp only at hcos hsin
  rw [RHTower.cosTaylor_ten_of_sq hs2, ← hC, ← hr] at hcos
  rw [RHTower.sinTaylor_ten_of_sq hs2, ← hS, ← hr] at hsin
  have hgap : C - (82749930 / 100000000 : ℝ) * S ≤ -(1 / 10 ^ 10) := by
    rw [hC, hS]
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hsinpos : 0 < Real.sin s := Real.sin_pos_of_pos_of_lt_pi hs0 (by linarith [Real.pi_gt_three])
  clear_value r S C s
  have hD : C - (82749930 / 100000000 : ℝ) * S + r < 0 := by linarith
  have hkey : s * Real.cos s ≤ (82749930 / 100000000 : ℝ) * Real.sin s := by
    have h1 : s * Real.cos s ≤ s * (C + r) := mul_le_mul_of_nonneg_left hcos hs0.le
    have h2 : s * (C - (82749930 / 100000000 : ℝ) * S + r)
        ≤ 7 / 10 * (C - (82749930 / 100000000 : ℝ) * S + r) :=
      mul_le_mul_of_nonpos_right hs7 hD.le
    have e1 : s * (C + r) = s * C + s * r := by ring
    have e2 : s * (C - (82749930 / 100000000 : ℝ) * S + r)
        = s * C - (82749930 / 100000000 : ℝ) * (s * S) + s * r := by ring
    have h3 : (82749930 / 100000000 : ℝ) * (s * S - r) ≤ (82749930 / 100000000 : ℝ) * Real.sin s :=
      mul_le_mul_of_nonneg_left hsin (by norm_num)
    linarith
  have hdiv : s * (Real.cos s / Real.sin s) ≤ 82749930 / 100000000 := by
    rw [← mul_div_assoc, div_le_iff₀ hsinpos]
    linarith
  linarith

/-- Explicit rational proportion `0.67250071 = 67250071 / 100000000` for simple critical-line zeros
of `ζ(s)`, strictly exceeding `0.6725007036… = HD(1)`. -/
theorem simple_critical_proportion_ge_67250071 :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (67250071 / 100000000 - ε) * (Zeta23.Ncount 0 T : ℝ) ≤ Zeta23.N0simple 0 T := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := beyond_HD_one_simple_critical_cumulative ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  have h := hT₀ T hT
  have hHD := HD_one_ge_67250070
  have hN0 : (0 : ℝ) ≤ Zeta23.Ncount 0 T := Nat.cast_nonneg _
  nlinarith

/-- Transport to the project's native completed-`ξ` simple critical-line census. -/
theorem beyond_montgomeryTaylor_xiSimpleCritical_epsilon :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Zeta23.ThmD.HD 1 + 1 / 10 ^ 8 - ε) * (RHTower.xiPosZeroCount T : ℝ)
        ≤ RHTower.xiSimpleCriticalZeroCount T := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := beyond_HD_one_simple_critical_cumulative ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  simpa only [RHTower.zeta23_Ncount_zero_eq_xiPosZeroCount,
    RHTower.zeta23_N0simple_zero_eq_xiSimpleCriticalZeroCount] using hT₀ T hT

/-- Transport to the project's native completed-`ξ` distinct-zero census. -/
theorem beyond_montgomeryTaylor_xiDistinct_epsilon :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Zeta23.ThmD.GD 1 + 1 / (2 * 10 ^ 8) - ε) * (RHTower.xiPosZeroCount T : ℝ)
        ≤ RHTower.xiPosDistinctZeroCount T := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := beyond_GD_one_distinct_cumulative ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  simpa only [RHTower.zeta23_Ncount_zero_eq_xiPosZeroCount,
    RHTower.zeta23_Ndist_zero_eq_xiPosDistinctZeroCount] using hT₀ T hT

/-- **Liminf form in the completed-`ξ` census: `HD(1) + 10⁻⁸ ≤ liminf N₀ˢ(T)/N(T)`.** -/
theorem HD_one_add_pos_le_liminf_xiSimpleCriticalRatio :
    Zeta23.ThmD.HD 1 + 1 / 10 ^ 8 ≤ Filter.liminf RHTower.xiSimpleCriticalRatio Filter.atTop := by
  set c : ℝ := Zeta23.ThmD.HD 1 + 1 / 10 ^ 8
  have hcob : IsCoboundedUnder (fun x y : ℝ => x ≥ y) atTop RHTower.xiSimpleCriticalRatio :=
    (isBoundedUnder_of ⟨1, fun T => RHTower.xiSimpleCriticalRatio_le_one T⟩).isCoboundedUnder_ge
  by_contra hnot
  have hlt : Filter.liminf RHTower.xiSimpleCriticalRatio atTop < c := lt_of_not_ge hnot
  let b : ℝ := (Filter.liminf RHTower.xiSimpleCriticalRatio atTop + c) / 2
  have hlim_b : Filter.liminf RHTower.xiSimpleCriticalRatio atTop < b := by dsimp [b]; linarith
  have hb_c : b < c := by dsimp [b]; linarith
  let ε : ℝ := c - b
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨T₀, hT₀⟩ := beyond_montgomeryTaylor_xiSimpleCritical_epsilon ε hε
  have hev : ∀ᶠ T : ℝ in atTop, b ≤ RHTower.xiSimpleCriticalRatio T := by
    filter_upwards [eventually_ge_atTop T₀, RHTower.eventually_pos_xiPosZeroCount_of_zeta23]
      with T hT hN
    rw [RHTower.xiSimpleCriticalRatio, le_div_iff₀ hN]
    have hbound := hT₀ T hT
    have heq : c - (c - b) = b := by ring
    rwa [show Zeta23.ThmD.HD 1 + 1 / 10 ^ 8 - ε = c - (c - b) from rfl, heq] at hbound
  have hb_liminf : b ≤ Filter.liminf RHTower.xiSimpleCriticalRatio atTop := le_liminf_of_le hcob hev
  linarith

end GaloisForLFunctions.IncommensurableGaborPinching
