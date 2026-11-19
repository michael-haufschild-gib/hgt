import GaloisForLFunctions.QuantitativeFactorizationMatching.PilotDebtEvacuationAndInvariantObstructions

/-!
# Provable Power Saving on a Self-Contained Growing Class of Cofactor Fibres

Unconditional construction of a growing, self-contained class of deficient ordered cofactor fibres
`balancedFibreClass X` on `(X, 2X]` that carries `Θ(X / (log X)³)` unmatched vertices under every
ordered-cofactor involution, yet admits an explicit closed `GlobalDyadicOneTwoRel` involution
leaving at most `4 * X^{113/180} ≤ 4 * X^{2/3}` unmatched vertices (and signed Möbius remainder at
most `4 * X^{113/180}`), saving more than `X^{1/3}` over the ordered-cofactor debt without any
positivity or spectral input.

## Mathematical mechanism

1. **Threshold-4/15 root cofactors (`balancedRootCofactors X`)**:
   Set `z = X^{1/180}` and take `b = q₁ * q₂` with `q₁ ∈ (3/4 z²⁸, z²⁸]` and
   `q₂ ∈ (3/4 z³², z³²]`. For `T_b = X / b` and `s = T_b^{1/120}`, the top prime factor `q₂` sits
   at exponent `32 / 120 = 4 / 15 < 1 / (e + 1)` of `T_b`. Slicing `(s³², s⁶⁰]` into `14`
   geometric bands `(s^{32+2i}, s^{34+2i}]` (`0 ≤ i < 14`) and applying concavity of `t(120 - t)`
   proves the strict positive surplus bounds
   `(1 / 1000) * T_b / log T_b ≤ #fibrePos(X, b) - #fibreNeg(X, b) ≤ (27 / 1000) * T_b / log T_b`.
2. **Empty-positive child pool (`balancedChildPool X b`) and prefix selection (`prefixSelect`)**:
   For `p₁ ∈ (s³², s³⁵]` and `p₂ ∈ (s³⁵, s⁴²]`, each child cofactor `a_- = b * p₁ * p₂` satisfies
   `fibrePos X a_- = ∅`, `#fibreNeg(X, a_-) ≤ ⌊2 s⁵³⌋₊`, and total negative supply across the
   rectangle exceeds `(27 / 1000) * T_b / log T_b`. Prefix selection (`balancedChildSelection X b`)
   matches `#fibrePos(X, b) - #fibreNeg(X, b)` up to a single fibre grain `≤ ⌊2 s⁵³⌋₊`.
3. **Closed cross-fibre `(1 ↔ 2)` involution and disjoint gluing**:
   Grouping child negative vertices `(b * p₁) * (p₂ * p₃)` by `p₁` places `(p₂, p₃)` inside the
   cube-root band of `X / (b * p₁)`, so `eventually_cubeBandProducts_nine_tenths` pairs 100% of
   child negatives into `{b * (p₁ * p)} ⊆ fibrePos X b` via `GlobalDyadicOneTwoRel` with unique
   factorization decoding (`maxPrimeStem`). Complete bipartiteness of `F_X(b)` pairs 100% of
   `fibreNeg X b` into the remaining `fibrePos X b` vertices, leaving `≤ ⌊2 s⁵³⌋₊ ≤ 4 z⁵³`
   unmatched vertices per root `b`. Gluing across disjoint `b ∈ balancedRootCofactors X` yields
   `≤ 4 * X^{113/180} ≤ 4 * X^{2/3}` unmatched vertices globally on `balancedFibreClass X`.
-/

open Finset Topology
open Filter (Tendsto atTop eventually_atTop eventually_ge_atTop tendsto_pow_atTop)
open _root_.RHTower _root_.RHTower.PrimeCells
open _root_.RHTower.Sieve (mertensBlockGapConst mertensFirst_general_block)
open scoped Classical BigOperators ArithmeticFunction.Moebius

noncomputable section

namespace GaloisForLFunctions.QuantitativeFactorizationMatching

/-! ### 1. Finite prefix selection up to a single-element grain -/

/-- Selects the longest ordered prefix of `C : Finset ℕ` whose `w`-weight sum is at most `D`. -/
def prefixSelect (C : Finset ℕ) (w : ℕ → ℕ) (D : ℕ) : Finset ℕ :=
  let cum : ℕ → ℕ := fun k => ∑ i ∈ range k, w (finsetEntry C i)
  let kMax : ℕ := ((range (C.card + 1)).filter fun k => cum k ≤ D).sup id
  (range kMax).image (finsetEntry C)

/-- **Prefix-selection approximation lemma**: if `D ≤ ∑ a ∈ C, w a` and every element of `C` has
weight `w a ≤ M`, then `prefixSelect C w D ⊆ C` satisfies
`∑ a ∈ prefixSelect C w D, w a ≤ D ≤ (∑ a ∈ prefixSelect C w D, w a) + M`. -/
theorem prefixSelect_spec {C : Finset ℕ} {w : ℕ → ℕ} {D M : ℕ}
    (hD : D ≤ ∑ a ∈ C, w a) (hM : ∀ a ∈ C, w a ≤ M) :
    prefixSelect C w D ⊆ C ∧
      (∑ a ∈ prefixSelect C w D, w a) ≤ D ∧
      D ≤ (∑ a ∈ prefixSelect C w D, w a) + M := by
  let cum : ℕ → ℕ := fun k => ∑ i ∈ range k, w (finsetEntry C i)
  let valid : Finset ℕ := (range (C.card + 1)).filter fun k => cum k ≤ D
  let kMax : ℕ := valid.sup id
  have h0_valid : 0 ∈ valid := by
    simp [valid, cum]
  have hne_valid : valid.Nonempty := ⟨0, h0_valid⟩
  have hkMax_eq : kMax = valid.max' hne_valid :=
    le_antisymm (Finset.sup_le fun k hk => le_max' _ k hk) (le_sup (f := id) (max'_mem _ hne_valid))
  have hkMax_mem : kMax ∈ valid := hkMax_eq ▸ max'_mem valid hne_valid
  have hkMax_le_card : kMax ≤ C.card := Nat.lt_succ_iff.mp (mem_range.mp (mem_filter.mp hkMax_mem).1)
  have hkMax_cum : cum kMax ≤ D := (mem_filter.mp hkMax_mem).2
  have hinj_range : ∀ {k : ℕ}, k ≤ C.card → Set.InjOn (finsetEntry C) ↑(range k) := by
    intro k hk i hi j hj heq
    exact finsetEntry_inj ((mem_range.mp hi).trans_le hk) ((mem_range.mp hj).trans_le hk) heq
  have hpref_sub : (range kMax).image (finsetEntry C) ⊆ C := by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := mem_image.mp ha
    exact finsetEntry_mem ((mem_range.mp hi).trans_le hkMax_le_card)
  have hpref_sum : ∑ a ∈ (range kMax).image (finsetEntry C), w a = cum kMax :=
    sum_image (hinj_range hkMax_le_card)
  have hfull_img : (range C.card).image (finsetEntry C) = C := by
    refine eq_of_subset_of_card_le ?_ ?_
    · intro a ha
      obtain ⟨i, hi, rfl⟩ := mem_image.mp ha
      exact finsetEntry_mem (mem_range.mp hi)
    · rw [card_image_of_injOn (hinj_range le_rfl), card_range]
  have hcum_full : cum C.card = ∑ a ∈ C, w a := by
    conv_rhs => rw [← hfull_img, sum_image (hinj_range le_rfl)]
  dsimp only [prefixSelect]
  change (range kMax).image (finsetEntry C) ⊆ C ∧
    (∑ a ∈ (range kMax).image (finsetEntry C), w a) ≤ D ∧
    D ≤ (∑ a ∈ (range kMax).image (finsetEntry C), w a) + M
  rw [hpref_sum]
  refine ⟨hpref_sub, hkMax_cum, ?_⟩
  rcases hkMax_le_card.eq_or_lt with htop | hlt
  · rw [htop, hcum_full]
    exact hD.trans (Nat.le_add_right _ M)
  · have hsucc_not : kMax + 1 ∉ valid := fun hmem =>
      (Nat.lt_succ_self kMax).not_ge (le_sup (f := id) hmem)
    have hsucc_range : kMax + 1 ∈ range (C.card + 1) := mem_range.mpr (Nat.succ_lt_succ hlt)
    have hgt : D < cum (kMax + 1) := by
      by_contra hle
      exact hsucc_not (mem_filter.mpr ⟨hsucc_range, not_lt.mp hle⟩)
    have hcum_succ : cum (kMax + 1) = cum kMax + w (finsetEntry C kMax) := sum_range_succ _ kMax
    have hw_le : w (finsetEntry C kMax) ≤ M := hM _ (finsetEntry_mem hlt)
    omega

/-! ### 2. Definitions of the growing self-contained fibre class -/

/-- Root cofactors `b = q₁ * q₂` with `q₁ ∈ (3/4 z²⁸, z²⁸]` and `q₂ ∈ (3/4 z³², z³²]`,
where `z = X^{1/180}` (`4 / 15 = 32 / 120 < 1 / (e + 1)` positive-surplus regime). -/
def balancedRootCofactors (X : ℕ) : Finset ℕ :=
  let z : ℝ := (X : ℝ) ^ (1 / 180 : ℝ)
  (windowPrimes ((3 / 4) * z ^ 28) (z ^ 28) ×ˢ
    windowPrimes ((3 / 4) * z ^ 32) (z ^ 32)).image fun pq => pq.1 * pq.2

/-- Pool of empty-positive child cofactors `a_- = b * p₁ * p₂` attached to a root `b`, with
`p₁ ∈ (s³², s³⁵]` and `p₂ ∈ (s³⁵, s⁴²]` (`s = (X / b)^{1/120}`). -/
def balancedChildPool (X b : ℕ) : Finset ℕ :=
  let s : ℝ := ((X : ℝ) / b) ^ (1 / 120 : ℝ)
  (windowPrimes (s ^ 32) (s ^ 35)).biUnion fun p₁ =>
    (windowPrimes (s ^ 35) (s ^ 42)).image fun p₂ => b * p₁ * p₂

/-- Exact prefix of `balancedChildPool X b` matching `#fibrePos(X, b) - #fibreNeg(X, b)` up to one
child fibre grain. -/
def balancedChildSelection (X b : ℕ) : Finset ℕ :=
  prefixSelect (balancedChildPool X b) (fun a => (fibreNeg X a).card)
    ((fibrePos X b).card - (fibreNeg X b).card)

/-- The growing, self-contained cofactor fibre class `A_*(X)` combining each root `b` with its
selected child empty-positive fibres `balancedChildSelection X b`. -/
def balancedFibreClass (X : ℕ) : Finset ℕ :=
  (balancedRootCofactors X).biUnion fun b => insert b (balancedChildSelection X b)

/-! ### 3. 14-slice rational constants and Mertens power-band estimates -/

private theorem lower_fourteen_slice_sum_ge :
    (10025 / 10000 : ℝ) ≤ ∑ i ∈ range 14, (60 : ℝ) / ((17 + (i : ℝ)) * (43 - (i : ℝ))) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

private theorem upper_fourteen_slice_sum_le :
    ∑ i ∈ range 14, (60 : ℝ) / ((16 + (i : ℝ)) * (44 - (i : ℝ))) ≤ (1022 / 1000 : ℝ) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

private theorem mertens_power_band_bounds {s : ℝ} {k m : ℕ} (hs : 2 ≤ s) (hk : 1 ≤ k)
    (hkm : k ≤ m) :
    ((m : ℝ) - k) * Real.log s - (Real.log 2 + mertensBlockGapConst) ≤
      ∑ p ∈ windowPrimes (s ^ k) (s ^ m), Real.log (p : ℝ) / (p : ℝ) ∧
    ∑ p ∈ windowPrimes (s ^ k) (s ^ m), Real.log (p : ℝ) / (p : ℝ) ≤
      ((m : ℝ) - k) * Real.log s + (Real.log 2 + mertensBlockGapConst) := by
  have hs0 : 0 < s := by linarith only [hs]
  have hsk_ge2 : 2 ≤ s ^ k := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
      _ ≤ s ^ k := pow_le_pow_left₀ (by norm_num) hs k
  have hsk_le_sm : s ^ k ≤ s ^ m := pow_le_pow_right₀ (by linarith only [hs]) hkm
  have hsm_ge2 : 2 ≤ s ^ m := hsk_ge2.trans hsk_le_sm
  let A := ⌊s ^ k⌋₊
  let B := ⌊s ^ m⌋₊
  have hA1 : 1 ≤ A := (Nat.one_le_floor_iff _).mpr (by linarith only [hsk_ge2])
  have hAB : A ≤ B := Nat.floor_le_floor hsk_le_sm
  have hA_lo : s ^ k / 2 ≤ (A : ℝ) := by
    have := Nat.lt_floor_add_one (s ^ k)
    dsimp [A]; linarith only [this, hsk_ge2]
  have hA_hi : (A : ℝ) ≤ s ^ k := Nat.floor_le (by positivity)
  have hB_lo : s ^ m / 2 ≤ (B : ℝ) := by
    have := Nat.lt_floor_add_one (s ^ m)
    dsimp [B]; linarith only [this, hsm_ge2]
  have hB_hi : (B : ℝ) ≤ s ^ m := Nat.floor_le (by positivity)
  have hlogA_lo : (k : ℝ) * Real.log s - Real.log 2 ≤ Real.log A := by
    have h := Real.log_le_log (by positivity) hA_lo
    rw [Real.log_div (by positivity) (by norm_num), Real.log_pow] at h
    linarith
  have hlogA_hi : Real.log A ≤ (k : ℝ) * Real.log s := by
    have h := Real.log_le_log (by exact_mod_cast hA1) hA_hi
    rwa [Real.log_pow] at h
  have hlogB_lo : (m : ℝ) * Real.log s - Real.log 2 ≤ Real.log B := by
    have h := Real.log_le_log (by positivity) hB_lo
    rw [Real.log_div (by positivity) (by norm_num), Real.log_pow] at h
    linarith
  have hlogB_hi : Real.log B ≤ (m : ℝ) * Real.log s := by
    have h := Real.log_le_log (by exact_mod_cast (hA1.trans hAB)) hB_hi
    rwa [Real.log_pow] at h
  rw [windowPrimes_eq_primesLE_sdiff_nat]
  exact ⟨by linarith [mertensFirst_general_block_ge hA1 hAB],
    by linarith [mertensFirst_general_block hA1 hAB]⟩

private lemma root_pos_lower_14slice (X b q₁ q₂ : ℕ) (T s H_lo : ℝ)
    (hX1 : 1 ≤ X) (hq₁ : q₁.Prime) (hq₂ : q₂.Prime) (hq₁₂ : q₁ < q₂) (hb_eq : b = q₁ * q₂)
    (hT_def : T = (X : ℝ) / b) (hs4 : 4 ≤ s) (hs120 : s ^ (120 : ℕ) = T)
    (hHs : H_lo ≤ s)
    (hL_mert : 40000 * (Real.log 2 + mertensBlockGapConst) ≤ Real.log s)
    (hq₂_hi : (q₂ : ℝ) ≤ s ^ 32)
    (hlo : ∀ R : ℝ, H_lo ≤ R → ∀ q : ℝ, 2 ≤ q → q ≤ 5 → ∀ u v : ℝ,
      R ≤ u → u ≤ v → v ≤ 2 * R → R / Real.log R ^ (0 : ℝ) ≤ v - u →
      (1 - 1 / 2000) * (v - u) / (q * Real.log R) ≤ ((windowPrimes (u / q) (v / q)).card : ℝ)) :
    (10017 / 10000) * T / Real.log T ≤ ((fibrePos X b).card : ℝ) := by
  have hs2 : 2 ≤ s := by linarith only [hs4]
  have hs1 : 1 ≤ s := by linarith only [hs4]
  have hs0 : 0 < s := by linarith only [hs4]
  have hb_pos : 0 < b := hb_eq ▸ Nat.mul_pos hq₁.pos hq₂.pos
  have hb_r : (0 : ℝ) < b := by exact_mod_cast hb_pos
  have hT_pos : 0 < T := by rw [hT_def]; exact div_pos (by exact_mod_cast hX1) hb_r
  obtain ⟨L, hL_def⟩ : ∃ L : ℝ, L = Real.log s := ⟨_, rfl⟩
  rw [← hL_def] at hL_mert
  have hL0 : 0 < L := by rw [hL_def]; exact Real.log_pos (by linarith only [hs4])
  have hlogT : Real.log T = 120 * L := by
    rw [← hs120, Real.log_pow, ← hL_def]; norm_num
  have hlogT_pos : 0 < Real.log T := by rw [hlogT]; positivity
  have hmert_nonneg : 0 ≤ mertensBlockGapConst := by
    have h := mertensFirst_general_block (A := 1) (B := 1) le_rfl le_rfl
    simp at h; linarith
  have hlog2_L : 40000 * Real.log 2 ≤ L := by linarith
  have hsq_b : Squarefree b := by
    rw [hb_eq]
    exact Nat.squarefree_mul_iff.mpr ⟨(Nat.coprime_primes hq₁ hq₂).mpr hq₁₂.ne,
      Irreducible.squarefree hq₁, Irreducible.squarefree hq₂⟩
  have htop_b : ∀ {p : ℕ}, q₂ < p → ∀ d ∈ b.primeFactors, d < p := by
    intro p hp d hd
    rw [hb_eq, Nat.primeFactors_mul hq₁.ne_zero hq₂.ne_zero, hq₁.primeFactors, hq₂.primeFactors] at hd
    rcases mem_union.mp hd with h1 | h2
    · rw [mem_singleton.mp h1]; exact hq₁₂.trans hp
    · rw [mem_singleton.mp h2]; exact hp
  have heven_b : Even b.primeFactors.card := by
    have ht : ∀ d ∈ q₁.primeFactors, d < q₂ := fun d hd =>
      (Nat.le_of_dvd hq₁.pos (Nat.dvd_of_mem_primeFactors hd)).trans_lt hq₁₂
    rw [hb_eq, card_primeFactors_mul_larger_prime hq₁.ne_zero hq₂ ht, hq₁.primeFactors, card_singleton]
    exact ⟨1, rfl⟩
  let Q_slice : ℕ → Finset ℕ := fun i => windowPrimes (s ^ (32 + 2 * i)) (s ^ (34 + 2 * i))
  let posRow : ℕ → Finset ℕ := fun q =>
    (windowPrimes (T / q) (2 * T / q)).image fun r => b * (q * r)
  have hrow_pos_sub : ∀ i ∈ range 14, ∀ q ∈ Q_slice i,
      posRow q ⊆ fibrePos X b ∧
      (∀ m ∈ posRow q, maxPrimeStem m = b * q) ∧
      (posRow q).card = (windowPrimes (T / q) (2 * T / q)).card := by
    intro i hi q hq
    have hi_lt : i < 14 := mem_range.mp hi
    obtain ⟨hqp, hq_lo, hq_hi⟩ := (mem_windowPrimes (by positivity) (by positivity)).mp hq
    have hq_0 : (0 : ℝ) < q := by exact_mod_cast hqp.pos
    have hs32_le : s ^ 32 ≤ s ^ (32 + 2 * i) := pow_le_pow_right₀ hs1 (by omega)
    have hq_le_s60 : (q : ℝ) ≤ s ^ 60 := hq_hi.trans (pow_le_pow_right₀ hs1 (by omega))
    have hq₂_lt_q : q₂ < q := by exact_mod_cast (hq₂_hi.trans hs32_le).trans_lt hq_lo
    have htop_q := htop_b hq₂_lt_q
    have hq_le_Tq : (q : ℝ) ≤ T / q := by
      rw [le_div_iff₀ hq_0, ← hs120]
      calc (q : ℝ) * q ≤ s ^ 60 * s ^ 60 :=
            mul_le_mul hq_le_s60 hq_le_s60 (by positivity) (by positivity)
        _ = s ^ 120 := by ring
    refine ⟨?_, ?_, card_image_of_injOn fun _ _ _ _ heq =>
      Nat.eq_of_mul_eq_mul_left hqp.pos (Nat.eq_of_mul_eq_mul_left hb_pos heq)⟩
    · intro m hm
      obtain ⟨r, hr_win, rfl⟩ := mem_image.mp hm
      obtain ⟨hrp, hr_lo, hr_hi⟩ := (mem_windowPrimes (by positivity) (by positivity)).mp hr_win
      have hqr : q < r := by exact_mod_cast hq_le_Tq.trans_lt hr_lo
      have htop_r := primeFactors_lt_of_mul_prime hb_pos.ne' hqp hqr htop_q
      have hμ_m : μ (b * (q * r)) = 1 := by
        rw [← mul_assoc,
          moebius_mul_larger_prime (Nat.mul_ne_zero hb_pos.ne' hqp.ne_zero) hrp htop_r,
          moebius_mul_larger_prime hb_pos.ne' hqp htop_q,
          moebius_eq_neg_one_pow_omega hsq_b, heven_b.neg_one_pow]; norm_num
      have hIoc : b * (q * r) ∈ Ioc X (2 * X) := by
        rw [hT_def, div_lt_iff₀ hq_0, div_lt_iff₀ hb_r] at hr_lo
        rw [hT_def, le_div_iff₀ hq_0, mul_div_assoc', le_div_iff₀ hb_r] at hr_hi
        have hcomm : ((b * (q * r) : ℕ) : ℝ) = (r : ℝ) * q * b := by push_cast; ring
        exact mem_Ioc.mpr ⟨by exact_mod_cast (show (X : ℝ) < ((b * (q * r) : ℕ) : ℝ) by rw [hcomm]; exact hr_lo),
          by exact_mod_cast (show ((b * (q * r) : ℕ) : ℝ) ≤ (2 * X : ℕ) by
            rw [hcomm, Nat.cast_mul 2 X, Nat.cast_ofNat]; exact hr_hi)⟩
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨hIoc, hμ_m⟩,
        evenPrefixCofactor_mul_ordered_pair hb_pos.ne' heven_b hqp hrp hqr htop_q⟩
    · intro m hm
      obtain ⟨r, hr_win, rfl⟩ := mem_image.mp hm
      obtain ⟨hrp, hr_lo, _⟩ := (mem_windowPrimes (by positivity) (by positivity)).mp hr_win
      have hqr : q < r := by exact_mod_cast hq_le_Tq.trans_lt hr_lo
      exact (maxPrimeStem_mul_pair hb_pos.ne' hqp hrp hqr htop_q).1
  have hQ_disj : (↑(range 14) : Set ℕ).PairwiseDisjoint Q_slice := by
    intro i hi j hj hne
    refine disjoint_left.mpr fun q hqi hqj => ?_
    obtain ⟨_, hlo_i, hhi_i⟩ := (mem_windowPrimes (by positivity) (by positivity)).mp hqi
    obtain ⟨_, hlo_j, hhi_j⟩ := (mem_windowPrimes (by positivity) (by positivity)).mp hqj
    rcases lt_or_gt_of_ne hne with hij | hji
    · have : s ^ (34 + 2 * i) ≤ s ^ (32 + 2 * j) := pow_le_pow_right₀ hs1 (by omega)
      linarith
    · have : s ^ (34 + 2 * j) ≤ s ^ (32 + 2 * i) := pow_le_pow_right₀ hs1 (by omega)
      linarith
  let Q_14 := (range 14).biUnion Q_slice
  have hpos_ge_14 : ∑ i ∈ range 14, ∑ q ∈ Q_slice i, (windowPrimes (T / q) (2 * T / q)).card ≤
      (fibrePos X b).card := by
    have hdisj_rows : (Q_14 : Set ℕ).PairwiseDisjoint posRow := by
      intro q₁' hq₁' q₂' hq₂' hne
      obtain ⟨i₁, hi₁, hqi₁⟩ := mem_biUnion.mp hq₁'
      obtain ⟨i₂, hi₂, hqi₂⟩ := mem_biUnion.mp hq₂'
      refine disjoint_left.mpr fun m hm₁ hm₂ => ?_
      have hs₁ := (hrow_pos_sub i₁ hi₁ q₁' hqi₁).2.1 m hm₁
      have hs₂ := (hrow_pos_sub i₂ hi₂ q₂' hqi₂).2.1 m hm₂
      exact hne (Nat.eq_of_mul_eq_mul_left hb_pos (hs₁.symm.trans hs₂))
    have hsub_all : Q_14.biUnion posRow ⊆ fibrePos X b := by
      intro m hm
      obtain ⟨q, hq, hmq⟩ := mem_biUnion.mp hm
      obtain ⟨i, hi, hqi⟩ := mem_biUnion.mp hq
      exact (hrow_pos_sub i hi q hqi).1 hmq
    calc ∑ i ∈ range 14, ∑ q ∈ Q_slice i, (windowPrimes (T / q) (2 * T / q)).card
        = ∑ i ∈ range 14, ∑ q ∈ Q_slice i, (posRow q).card :=
          sum_congr rfl fun i hi => sum_congr rfl fun q hq => (hrow_pos_sub i hi q hq).2.2.symm
      _ = ∑ q ∈ Q_14, (posRow q).card := (sum_biUnion hQ_disj).symm
      _ = (Q_14.biUnion posRow).card := (card_biUnion hdisj_rows).symm
      _ ≤ (fibrePos X b).card := card_le_card hsub_all
  have hslice_lo : ∀ i ∈ range 14,
      (9993 / 10000) * ((60 : ℝ) / ((17 + (i : ℝ)) * (43 - (i : ℝ)))) * (T / Real.log T) ≤
        ∑ q ∈ Q_slice i, ((windowPrimes (T / q) (2 * T / q)).card : ℝ) := by
    intro i hi
    have hi_lt : i < 14 := mem_range.mp hi
    have hi_r : (i : ℝ) ≤ 13 := by exact_mod_cast (Nat.lt_succ_iff.mp hi_lt)
    have hden_pos : 0 < (17 + (i : ℝ)) * (43 - (i : ℝ)) := by nlinarith only [hi_r]
    have h60_i : (34 + 2 * (i : ℝ)) * L ≤ 60 * L :=
      mul_le_mul_of_nonneg_right (by linarith only [hi_r]) hL0.le
    have hrow_lo : ∀ q ∈ Q_slice i,
        (1999 / 2000) * (20000 / 20001) *
          (T / (4 * ((17 + (i : ℝ)) * (43 - (i : ℝ))) * L ^ 2)) *
          (Real.log (q : ℝ) / (q : ℝ)) ≤
            ((windowPrimes (T / q) (2 * T / q)).card : ℝ) := by
      intro q hq
      obtain ⟨hqp, hq_lo, hq_hi⟩ := (mem_windowPrimes (by positivity) (by positivity)).mp hq
      have hq_0 : (0 : ℝ) < q := by exact_mod_cast hqp.pos
      have hq_s60 : (q : ℝ) ≤ s ^ 60 := hq_hi.trans (pow_le_pow_right₀ hs1 (by omega))
      have hTq_ge_s : s ≤ T / q := by
        rw [le_div_iff₀ hq_0, ← hs120]
        calc s * q ≤ s ^ 60 * s ^ 60 :=
              mul_le_mul (by simpa only [pow_one] using pow_le_pow_right₀ hs1 (by decide : 1 ≤ 60))
                hq_s60 (by positivity) (by positivity)
          _ = s ^ 120 := by ring
      have hlq_pos : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hqp.one_lt)
      have hlq_hi : Real.log (q : ℝ) ≤ (34 + 2 * (i : ℝ)) * L := by
        have h := Real.log_le_log hq_0 hq_hi
        rw [Real.log_pow, ← hL_def] at h; push_cast at h; exact h
      have hlq_60 : Real.log (q : ℝ) ≤ 60 * L := hlq_hi.trans h60_i
      have hl2Tq : Real.log (2 * (T / q)) ≤ (20001 / 20000) * (120 * L - Real.log (q : ℝ)) := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_div hT_pos.ne' hq_0.ne', hlogT]
        linarith only [hlog2_L, hlq_60, hL0]
      have hconc : Real.log (q : ℝ) * (120 * L - Real.log (q : ℝ)) ≤
          4 * ((17 + (i : ℝ)) * (43 - (i : ℝ))) * L ^ 2 := by
        have hdiff : 4 * ((17 + (i : ℝ)) * (43 - (i : ℝ))) * L ^ 2 -
            Real.log (q : ℝ) * (120 * L - Real.log (q : ℝ)) =
          ((34 + 2 * (i : ℝ)) * L - Real.log (q : ℝ)) *
            (120 * L - (34 + 2 * (i : ℝ)) * L - Real.log (q : ℝ)) := by ring
        have hf1 : 0 ≤ (34 + 2 * (i : ℝ)) * L - Real.log (q : ℝ) := by linarith only [hlq_hi]
        have hf2 : 0 ≤ 120 * L - (34 + 2 * (i : ℝ)) * L - Real.log (q : ℝ) := by
          linarith only [hlq_60, h60_i]
        linarith only [hdiff, mul_nonneg hf1 hf2]
      have hprod_le : Real.log (q : ℝ) * Real.log (2 * (T / q)) ≤
          (20001 / 20000) * (4 * ((17 + (i : ℝ)) * (43 - (i : ℝ))) * L ^ 2) :=
        (mul_le_mul_of_nonneg_left hl2Tq hlq_pos.le).trans
          ((mul_left_comm _ _ _).trans_le (mul_le_mul_of_nonneg_left hconc (by positivity)))
      have hTq_pos : 0 < T / q := div_pos hT_pos hq_0
      have hw := hlo (2 * (T / q)) (hHs.trans (hTq_ge_s.trans (by linarith only [hs0, hTq_ge_s])))
        2 (by norm_num) (by norm_num) (2 * (T / q)) (4 * (T / q))
        le_rfl (by linarith only [hTq_pos]) (by linarith only [hTq_pos])
        (by rw [Real.rpow_zero, div_one]; linarith only [hTq_pos])
      have hd1 : 2 * (T / q) / 2 = T / q := by ring
      have hd2 : 4 * (T / q) / 2 = 2 * T / q := by ring
      rw [hd1, hd2] at hw
      refine le_trans ?_ hw
      have hrhs_eq : (1 - 1 / 2000) * (4 * (T / q) - 2 * (T / q)) /
          (2 * Real.log (2 * (T / q))) =
          (1999 / 2000) * T * Real.log (q : ℝ) /
            ((q : ℝ) * (Real.log (q : ℝ) * Real.log (2 * (T / q)))) := by field_simp; ring
      rw [hrhs_eq]
      have hlhs_eq : (1999 / 2000) * (20000 / 20001) *
          (T / (4 * ((17 + (i : ℝ)) * (43 - (i : ℝ))) * L ^ 2)) *
          (Real.log (q : ℝ) / (q : ℝ)) =
          (1999 / 2000) * T * Real.log (q : ℝ) /
            ((q : ℝ) * ((20001 / 20000) * (4 * ((17 + (i : ℝ)) * (43 - (i : ℝ))) * L ^ 2))) := by
        field_simp
      rw [hlhs_eq]
      exact div_le_div_of_nonneg_left (by positivity)
        (mul_pos hq_0 (mul_pos hlq_pos (Real.log_pos (by linarith only [hs4, hTq_ge_s]))))
        (mul_le_mul_of_nonneg_left hprod_le hq_0.le)
    have hmert := (mertens_power_band_bounds hs2 (by omega : 1 ≤ 32 + 2 * i)
      (by omega : 32 + 2 * i ≤ 34 + 2 * i)).1
    have hdiff_k : ((34 + 2 * i : ℕ) : ℝ) - ((32 + 2 * i : ℕ) : ℝ) = 2 := by push_cast; ring
    rw [hdiff_k, ← hL_def] at hmert
    have hmert_lo : (19999 / 20000) * (2 * L) ≤
        ∑ q ∈ Q_slice i, Real.log (q : ℝ) / (q : ℝ) := by linarith only [hmert, hL_mert, hL0]
    have hsum_step := (sum_le_sum hrow_lo).trans_eq rfl
    rw [← mul_sum] at hsum_step
    refine le_trans ?_ ((mul_le_mul_of_nonneg_left hmert_lo (by positivity)).trans hsum_step)
    rw [hlogT]
    have hnum_rat : (9993 / 10000 : ℝ) ≤ (1999 / 2000) * (20000 / 20001) * (19999 / 20000) := by
      norm_num
    have hident : (1999 / 2000 : ℝ) * (20000 / 20001) *
        (T / (4 * ((17 + (i : ℝ)) * (43 - (i : ℝ))) * L ^ 2)) *
        ((19999 / 20000) * (2 * L)) =
        ((1999 / 2000) * (20000 / 20001) * (19999 / 20000)) *
          (((60 : ℝ) / ((17 + (i : ℝ)) * (43 - (i : ℝ)))) * (T / (120 * L))) := by
      field_simp; ring
    rw [hident, mul_assoc]
    exact mul_le_mul_of_nonneg_right hnum_rat
      (mul_nonneg (div_nonneg (by positivity) hden_pos.le) (by positivity))
  have hsum14 := sum_le_sum hslice_lo
  simp only [mul_assoc, ← mul_sum, ← sum_mul] at hsum14
  have h10025 := lower_fourteen_slice_sum_ge
  calc (10017 / 10000) * T / Real.log T
      ≤ (9993 / 10000) * ((10025 / 10000) * (T / Real.log T)) := by
        rw [mul_div_assoc, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    _ ≤ (9993 / 10000) *
          ((∑ i ∈ range 14, (60 : ℝ) / ((17 + (i : ℝ)) * (43 - (i : ℝ)))) *
            (T / Real.log T)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h10025 (by positivity))
          (by positivity)
    _ ≤ ∑ i ∈ range 14, ∑ q ∈ Q_slice i, ((windowPrimes (T / q) (2 * T / q)).card : ℝ) := by
        simpa only [mul_assoc, sum_mul] using hsum14
    _ ≤ ((fibrePos X b).card : ℝ) := by exact_mod_cast hpos_ge_14

private lemma root_pos_upper_collar_and_cap (X b q₁ q₂ : ℕ) (T s A_up : ℝ)
    (hX1 : 1 ≤ X) (hq₁ : q₁.Prime) (hq₂ : q₂.Prime) (hb_eq : b = q₁ * q₂)
    (hT_def : T = (X : ℝ) / b) (hs4 : 4 ≤ s) (hs120 : s ^ (120 : ℕ) = T)
    (hAs : 2 * A_up ≤ s)
    (hL_mert : 40000 * (Real.log 2 + mertensBlockGapConst) ≤ Real.log s)
    (hL_col : 2000000 * ((Real.log (16 / 9) + Real.log 2 + mertensBlockGapConst) +
      2 * Real.log 2 + mertensBlockGapConst) ≤ Real.log s)
    (hq₂_lo : (9 / 16) * s ^ 32 < (q₂ : ℝ))
    (hup : ∀ R : ℝ, A_up ≤ R → ∀ u v : ℝ, R ≤ u → u ≤ v → v ≤ 2 * R →
      R / Real.log R ^ (0 : ℝ) ≤ v - u →
      ((windowPrimes u v).card : ℝ) ≤ (1 + 1 / 2000) * (v - u) / Real.log R) :
    ((fibrePos X b).card : ℝ) ≤
      (1 / 1000) * T / Real.log T +
      ∑ i ∈ range 14, ∑ q ∈ windowPrimes (s ^ (32 + 2 * i)) (s ^ (34 + 2 * i)),
        ((windowPrimes (T / q) (2 * T / q)).card : ℝ) := by
  have hs1 : 1 ≤ s := by linarith only [hs4]
  have hs0 : 0 < s := by linarith only [hs4]
  have hb_pos : 0 < b := hb_eq ▸ Nat.mul_pos hq₁.pos hq₂.pos
  have hb_r : (0 : ℝ) < b := by exact_mod_cast hb_pos
  have hT_pos : 0 < T := by rw [hT_def]; exact div_pos (by exact_mod_cast hX1) hb_r
  obtain ⟨L, hL_def⟩ : ∃ L : ℝ, L = Real.log s := ⟨_, rfl⟩
  rw [← hL_def] at hL_mert hL_col
  have hL0 : 0 < L := by rw [hL_def]; exact Real.log_pos (by linarith only [hs4])
  have hlogT : Real.log T = 120 * L := by
    rw [← hs120, Real.log_pow, ← hL_def]; norm_num
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmert_nonneg : 0 ≤ mertensBlockGapConst := by
    have h := mertensFirst_general_block (A := 1) (B := 1) le_rfl le_rfl
    simp at h; linarith only [h]
  have hlog2_L : 40000 * Real.log 2 ≤ L := by linarith only [hL_mert, hmert_nonneg]
  let C_col : ℝ := Real.log (16 / 9) + Real.log 2 + mertensBlockGapConst
  let Q_slice : ℕ → Finset ℕ := fun i => windowPrimes (s ^ (32 + 2 * i)) (s ^ (34 + 2 * i))
  have hQ_disj : (↑(range 14) : Set ℕ).PairwiseDisjoint Q_slice := by
    intro i hi j hj hne
    refine disjoint_left.mpr fun q hqi hqj => ?_
    obtain ⟨_, hlo_i, hhi_i⟩ := (mem_windowPrimes (by positivity) (by positivity)).mp hqi
    obtain ⟨_, hlo_j, hhi_j⟩ := (mem_windowPrimes (by positivity) (by positivity)).mp hqj
    rcases lt_or_gt_of_ne hne with hij | hji
    · have hp : s ^ (34 + 2 * i) ≤ s ^ (32 + 2 * j) := pow_le_pow_right₀ hs1 (by omega)
      linarith only [hlo_j, hhi_i, hp]
    · have hp : s ^ (34 + 2 * j) ≤ s ^ (32 + 2 * i) := pow_le_pow_right₀ hs1 (by omega)
      linarith only [hlo_i, hhi_j, hp]
  let Q_14 := (range 14).biUnion Q_slice
  let Q_col := windowPrimes ((9 / 16) * s ^ 32) (s ^ 32)
  let Q_cap := windowPrimes (s ^ 60) (2 * s ^ 60)
  have hpos_cover : (fibrePos X b).card ≤
      (∑ q ∈ Q_col, (windowPrimes (T / q) (2 * T / q)).card) +
      (∑ i ∈ range 14, ∑ q ∈ Q_slice i, (windowPrimes (T / q) (2 * T / q)).card) +
      (∑ q ∈ Q_cap, (windowPrimes (T / q) (2 * T / q)).card) := by
    let Q_all := Q_col ∪ Q_14 ∪ Q_cap
    have hdiv_sub : (fibrePos X b).image (· / b) ⊆
        Q_all.biUnion fun q => (windowPrimes (T / q) (2 * T / q)).image (q * ·) := by
      intro w hw
      obtain ⟨m, hm, rfl⟩ := mem_image.mp hw
      obtain ⟨_, _, q, r, hqp, hrp, hqr, hmb, hlt_q⟩ := mem_fibrePos_structure hX1 hm
      obtain ⟨hm_lo, hm_hi⟩ := mem_Ioc.mp (mem_filter.mp (mem_filter.mp hm).1).1
      have hdiv_eq : m / b = q * r := by rw [hmb, mul_comm b, Nat.mul_div_cancel _ hb_pos]
      rw [hdiv_eq]
      have hq_0 : (0 : ℝ) < q := by exact_mod_cast hqp.pos
      have hq_gt_col : (9 / 16) * s ^ 32 < (q : ℝ) :=
        hq₂_lo.trans (by exact_mod_cast hlt_q q₂ (Nat.mem_primeFactors.mpr
          ⟨hq₂, hb_eq ▸ dvd_mul_left q₂ q₁, hb_pos.ne'⟩))
      have hprod_hi : (q : ℝ) * r ≤ 2 * T := by
        rw [hT_def, mul_div_assoc', le_div_iff₀ hb_r]
        exact_mod_cast (show (q * r) * b ≤ 2 * X by rw [mul_comm, ← hmb]; exact hm_hi)
      have hq_le_2s60 : (q : ℝ) ≤ 2 * s ^ 60 := by
        have hq2 : (q : ℝ) ^ 2 ≤ 2 * s ^ 120 := by
          rw [hs120]
          exact (show (q : ℝ) ^ 2 ≤ (q : ℝ) * r by
            rw [sq]; exact mul_le_mul_of_nonneg_left (by exact_mod_cast hqr.le) (Nat.cast_nonneg q)).trans hprod_hi
        by_contra hgt; push Not at hgt
        nlinarith only [hq2, hgt, pow_nonneg hs0.le 60, pow_nonneg hs0.le 120]
      have hq_all : q ∈ Q_all := by
        by_cases h1 : (q : ℝ) ≤ s ^ 32
        · exact mem_union_left _ (mem_union_left _
            ((mem_windowPrimes (by positivity) (by positivity)).mpr ⟨hqp, hq_gt_col, h1⟩))
        · push Not at h1
          by_cases h2 : (q : ℝ) ≤ s ^ 60
          · have hex_i : ∃ i ∈ range 14, q ∈ Q_slice i := by
              by_contra hnone; push Not at hnone
              have hind : ∀ k : ℕ, k ≤ 14 → s ^ (32 + 2 * k) < (q : ℝ) := by
                intro k hk
                induction k with
                | zero => simpa using h1
                | succ k ih =>
                  have hk_lt : k < 14 := Nat.lt_of_succ_le hk
                  have hprev := ih hk_lt.le
                  by_contra hle; push Not at hle
                  exact hnone k (mem_range.mpr hk_lt)
                    ((mem_windowPrimes (by positivity) (by positivity)).mpr ⟨hqp, hprev,
                      by rwa [show 34 + 2 * k = 32 + 2 * (k + 1) by omega]⟩)
              have h14 := hind 14 le_rfl
              rw [show 32 + 2 * 14 = 60 by decide] at h14
              linarith only [h2, h14]
            obtain ⟨i, hi, hqi⟩ := hex_i
            exact mem_union_left _ (mem_union_right _ (mem_biUnion.mpr ⟨i, hi, hqi⟩))
          · push Not at h2
            exact mem_union_right _
              ((mem_windowPrimes (by positivity) (by positivity)).mpr ⟨hqp, h2, hq_le_2s60⟩)
      refine mem_biUnion.mpr ⟨q, hq_all,
        mem_image.mpr ⟨r, (mem_windowPrimes (by positivity) (by positivity)).mpr ⟨hrp, ?_, ?_⟩, rfl⟩⟩
      · rw [hT_def, div_lt_iff₀ hq_0, div_lt_iff₀ hb_r]
        exact_mod_cast (show X < r * q * b by
          rw [show r * q * b = b * (q * r) by ring, ← hmb]; exact hm_lo)
      · rw [hT_def, le_div_iff₀ hq_0, mul_div_assoc', le_div_iff₀ hb_r]
        exact_mod_cast (show r * q * b ≤ 2 * X by
          rw [show r * q * b = b * (q * r) by ring, ← hmb]; exact hm_hi)
    have hdiv_inj : Set.InjOn (· / b) ↑(fibrePos X b) := by
      intro m₁ hm₁ m₂ hm₂ heq
      dsimp only at heq
      obtain ⟨_, _, r₁, r₂, _, _, _, hmb₁, _⟩ := mem_fibrePos_structure hX1 hm₁
      obtain ⟨_, _, r₁', r₂', _, _, _, hmb₂, _⟩ := mem_fibrePos_structure hX1 hm₂
      have hd₁ : m₁ / b = r₁ * r₂ := by rw [hmb₁, mul_comm, Nat.mul_div_cancel _ hb_pos]
      have hd₂ : m₂ / b = r₁' * r₂' := by rw [hmb₂, mul_comm, Nat.mul_div_cancel _ hb_pos]
      rw [hmb₁, hmb₂, ← hd₁, ← hd₂, heq]
    rw [← card_image_of_injOn hdiv_inj]
    refine (card_le_card hdiv_sub).trans ?_
    refine (card_biUnion_le.trans (sum_le_sum fun q _ => card_image_le)).trans ?_
    dsimp only [Q_all]
    have hu1 := Finset.sum_union_inter (s₁ := Q_col ∪ Q_14) (s₂ := Q_cap)
      (f := fun q => (windowPrimes (T / q) (2 * T / q)).card)
    have hu2 := Finset.sum_union_inter (s₁ := Q_col) (s₂ := Q_14)
      (f := fun q => (windowPrimes (T / q) (2 * T / q)).card)
    have hu3 : ∑ q ∈ Q_14, (windowPrimes (T / q) (2 * T / q)).card =
        ∑ i ∈ range 14, ∑ q ∈ Q_slice i, (windowPrimes (T / q) (2 * T / q)).card :=
      sum_biUnion hQ_disj
    omega
  have hcol_hi : (∑ q ∈ Q_col, ((windowPrimes (T / q) (2 * T / q)).card : ℝ)) ≤
      (1 / 2000) * T / Real.log T := by
    have hrow : ∀ q ∈ Q_col, ((windowPrimes (T / q) (2 * T / q)).card : ℝ) ≤
        (2 * T / (31 * 88 * L ^ 2)) * (Real.log (q : ℝ) / (q : ℝ)) := by
      intro q hq
      obtain ⟨hqp, hq_lo, hq_hi⟩ := (mem_windowPrimes (by positivity) (by positivity)).mp hq
      have hq_0 : (0 : ℝ) < q := by exact_mod_cast hqp.pos
      have hlq_pos : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hqp.one_lt)
      have hTq_ge_s : s ≤ T / q := by
        rw [le_div_iff₀ hq_0, ← hs120]
        calc s * q ≤ s * s ^ 32 := mul_le_mul_of_nonneg_left hq_hi hs0.le
          _ = s ^ 33 := by ring
          _ ≤ s ^ 120 := pow_le_pow_right₀ hs1 (by decide)
      have hlq_ge : 31 * L ≤ Real.log (q : ℝ) := by
        have h916 : s ^ 31 ≤ (9 / 16) * s ^ 32 := by
          calc s ^ 31 ≤ (9 / 4) * s ^ 31 := by linarith [pow_pos hs0 31]
            _ = (9 / 16) * (4 * s ^ 31) := by ring
            _ ≤ (9 / 16) * (s * s ^ 31) := by gcongr
            _ = (9 / 16) * s ^ 32 := by ring
        have h := Real.log_le_log (by positivity) (h916.trans hq_lo.le)
        rwa [Real.log_pow, ← hL_def, show ((31 : ℕ) : ℝ) = 31 by norm_num] at h
      have hlTq_ge : 88 * L ≤ Real.log (T / q) := by
        rw [Real.log_div hT_pos.ne' hq_0.ne', hlogT]
        have h := Real.log_le_log hq_0 hq_hi
        rw [Real.log_pow, ← hL_def] at h; norm_num1 at h; linarith only [h]
      have hlTq_pos : 0 < Real.log (T / q) := by linarith only [hlTq_ge, hL0]
      have hdiff : 2 * T / (q : ℝ) - T / q = T / q := by ring
      have hw := hup (T / q) ((by linarith only [hAs, hs0] : A_up ≤ s).trans hTq_ge_s)
        (T / q) (2 * T / q) le_rfl (by rw [mul_div_assoc]; linarith [div_pos hT_pos hq_0])
        (by rw [mul_div_assoc]) (by rw [Real.rpow_zero, div_one, hdiff])
      rw [hdiff] at hw
      refine hw.trans ?_
      have hprod : 31 * 88 * L ^ 2 ≤ Real.log (q : ℝ) * Real.log (T / q) := by
        calc 31 * 88 * L ^ 2 = (31 * L) * (88 * L) := by ring
          _ ≤ Real.log (q : ℝ) * Real.log (T / q) :=
              mul_le_mul hlq_ge hlTq_ge (by positivity) hlq_pos.le
      have hlhs_le : (1 + 1 / 2000) * (T / q) / Real.log (T / q) ≤
          2 * (T / q) / Real.log (T / q) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by norm_num) (by positivity)) hlTq_pos.le
      refine hlhs_le.trans ?_
      have heq1 : 2 * (T / q) / Real.log (T / q) =
          (2 * T * Real.log (q : ℝ)) / ((q : ℝ) * (Real.log (q : ℝ) * Real.log (T / q))) := by
        field_simp
      have heq2 : (2 * T / (31 * 88 * L ^ 2)) * (Real.log (q : ℝ) / (q : ℝ)) =
          (2 * T * Real.log (q : ℝ)) / ((q : ℝ) * (31 * 88 * L ^ 2)) := by
        field_simp
      rw [heq1, heq2]
      exact div_le_div_of_nonneg_left (by positivity)
        (mul_pos hq_0 (by positivity)) (mul_le_mul_of_nonneg_left hprod hq_0.le)
    have hmert_col : ∑ q ∈ Q_col, Real.log (q : ℝ) / (q : ℝ) ≤ C_col := by
      let A := ⌊(9 / 16) * s ^ 32⌋₊
      let B := ⌊s ^ 32⌋₊
      have h916_ge2 : 2 ≤ (9 / 16) * s ^ 32 := by
        have h4s : (4 : ℝ) ≤ s ^ 32 := by
          calc (4 : ℝ) = 4 ^ 1 := by norm_num
            _ ≤ s ^ 1 := by gcongr
            _ ≤ s ^ 32 := pow_le_pow_right₀ hs1 (by decide)
        linarith only [h4s]
      have hA1 : 1 ≤ A := (Nat.one_le_floor_iff _).mpr (by linarith only [h916_ge2])
      have hAB : A ≤ B := Nat.floor_le_floor (by linarith [pow_pos hs0 32])
      have hA_lo : (9 / 32) * s ^ 32 ≤ (A : ℝ) := by
        have hf := Nat.lt_floor_add_one ((9 / 16) * s ^ 32)
        dsimp [A]; linarith only [hf, h916_ge2]
      have hB_hi : (B : ℝ) ≤ s ^ 32 := Nat.floor_le (by positivity)
      have hlA : Real.log ((9 / 32) * s ^ 32) ≤ Real.log A :=
        Real.log_le_log (by positivity) hA_lo
      have hlB : Real.log B ≤ 32 * L := by
        have h := Real.log_le_log (by exact_mod_cast (hA1.trans hAB)) hB_hi
        rwa [Real.log_pow, ← hL_def, show ((32 : ℕ) : ℝ) = 32 by norm_num] at h
      have hsplit : Real.log ((9 / 32) * s ^ 32) = 32 * L - Real.log (16 / 9) - Real.log 2 := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, ← hL_def]
        have : Real.log (9 / 32 : ℝ) = -Real.log (16 / 9) - Real.log 2 := by
          have h1 : (9 / 32 : ℝ) = ((16 / 9) * 2)⁻¹ := by norm_num
          rw [h1, Real.log_inv, Real.log_mul (by norm_num) (by norm_num)]; ring
        rw [this]; norm_num; ring
      rw [hsplit] at hlA
      dsimp only [Q_col]
      rw [windowPrimes_eq_primesLE_sdiff_nat]
      dsimp [C_col]
      linarith [mertensFirst_general_block hA1 hAB]
    have hsum := (sum_le_sum hrow).trans
      ((mul_sum _ _ _).symm.trans_le (mul_le_mul_of_nonneg_left hmert_col (by positivity)))
    refine hsum.trans ?_
    rw [hlogT]
    have hCcol_L : C_col ≤ (1 / 2000000) * L := by
      dsimp [C_col]; linarith only [hL_col, hlog2_pos, hmert_nonneg]
    calc (2 * T / (31 * 88 * L ^ 2)) * C_col
        ≤ (2 * T / (31 * 88 * L ^ 2)) * ((1 / 2000000) * L) :=
          mul_le_mul_of_nonneg_left hCcol_L (by positivity)
      _ = (240 / (31 * 88 * 2000000 : ℝ)) * (T / (120 * L)) := by field_simp; ring
      _ ≤ (1 / 2000) * (T / (120 * L)) :=
          mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ = (1 / 2000) * T / (120 * L) := by ring
  have hcap_hi : (∑ q ∈ Q_cap, ((windowPrimes (T / q) (2 * T / q)).card : ℝ)) ≤
      (1 / 2000) * T / Real.log T := by
    have hrow : ∀ q ∈ Q_cap, ((windowPrimes (T / q) (2 * T / q)).card : ℝ) ≤
        (2 * T / (60 * 59 * L ^ 2)) * (Real.log (q : ℝ) / (q : ℝ)) := by
      intro q hq
      obtain ⟨hqp, hq_lo, hq_hi⟩ := (mem_windowPrimes (by positivity) (by positivity)).mp hq
      have hq_0 : (0 : ℝ) < q := by exact_mod_cast hqp.pos
      have hlq_pos : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hqp.one_lt)
      have hTq_ge_A : A_up ≤ T / q := by
        rw [le_div_iff₀ hq_0]
        have hs59 : 2 * s ≤ s ^ 60 := by
          calc 2 * s ≤ s * s := by nlinarith only [hs4]
            _ = s ^ 2 := by ring
            _ ≤ s ^ 60 := pow_le_pow_right₀ hs1 (by decide)
        calc A_up * q ≤ (s / 2) * (2 * s ^ 60) :=
              mul_le_mul (by linarith only [hAs]) hq_hi (by positivity) (by positivity)
          _ = s * s ^ 60 := by ring
          _ ≤ s ^ 60 * s ^ 60 :=
              mul_le_mul_of_nonneg_right (by linarith only [hs59, hs0]) (by positivity)
          _ = T := by rw [← hs120]; ring
      have hlq_ge : 60 * L ≤ Real.log (q : ℝ) := by
        have h := Real.log_le_log (by positivity) hq_lo.le
        rwa [Real.log_pow, ← hL_def, show ((60 : ℕ) : ℝ) = 60 by norm_num] at h
      have hlTq_ge : 59 * L ≤ Real.log (T / q) := by
        rw [Real.log_div hT_pos.ne' hq_0.ne', hlogT]
        have h := Real.log_le_log hq_0 hq_hi
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, ← hL_def] at h
        norm_num1 at h; linarith only [h, hlog2_L, hL0]
      have hlTq_pos : 0 < Real.log (T / q) := by linarith only [hlTq_ge, hL0]
      have hdiff : 2 * T / (q : ℝ) - T / q = T / q := by ring
      have hw := hup (T / q) hTq_ge_A (T / q) (2 * T / q) le_rfl
        (by rw [mul_div_assoc]; linarith [div_pos hT_pos hq_0])
        (by rw [mul_div_assoc]) (by rw [Real.rpow_zero, div_one, hdiff])
      rw [hdiff] at hw
      refine hw.trans ?_
      have hprod : 60 * 59 * L ^ 2 ≤ Real.log (q : ℝ) * Real.log (T / q) := by
        calc 60 * 59 * L ^ 2 = (60 * L) * (59 * L) := by ring
          _ ≤ Real.log (q : ℝ) * Real.log (T / q) :=
              mul_le_mul hlq_ge hlTq_ge (by positivity) hlq_pos.le
      have hlhs_le : (1 + 1 / 2000) * (T / q) / Real.log (T / q) ≤
          2 * (T / q) / Real.log (T / q) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by norm_num) (by positivity)) hlTq_pos.le
      refine hlhs_le.trans ?_
      have heq1 : 2 * (T / q) / Real.log (T / q) =
          (2 * T * Real.log (q : ℝ)) / ((q : ℝ) * (Real.log (q : ℝ) * Real.log (T / q))) := by
        field_simp
      have heq2 : (2 * T / (60 * 59 * L ^ 2)) * (Real.log (q : ℝ) / (q : ℝ)) =
          (2 * T * Real.log (q : ℝ)) / ((q : ℝ) * (60 * 59 * L ^ 2)) := by
        field_simp
      rw [heq1, heq2]
      exact div_le_div_of_nonneg_left (by positivity)
        (mul_pos hq_0 (by positivity)) (mul_le_mul_of_nonneg_left hprod hq_0.le)
    have hmert_cap : ∑ q ∈ Q_cap, Real.log (q : ℝ) / (q : ℝ) ≤
        2 * Real.log 2 + mertensBlockGapConst := by
      let A := ⌊s ^ 60⌋₊
      let B := ⌊2 * s ^ 60⌋₊
      have hs60_ge2 : 2 ≤ s ^ 60 := by
        calc (2 : ℝ) ≤ s ^ 1 := by simpa only [pow_one] using (by linarith only [hs4] : 2 ≤ s)
          _ ≤ s ^ 60 := pow_le_pow_right₀ hs1 (by decide)
      have hA1 : 1 ≤ A := (Nat.one_le_floor_iff _).mpr (by linarith only [hs60_ge2])
      have hAB : A ≤ B := Nat.floor_le_floor (by linarith only [hs60_ge2])
      have hlA : 60 * L - Real.log 2 ≤ Real.log A := by
        have hA_lo : s ^ 60 / 2 ≤ (A : ℝ) := by
          have hf := Nat.lt_floor_add_one (s ^ 60); dsimp [A]; linarith only [hf, hs60_ge2]
        have h := Real.log_le_log (by positivity) hA_lo
        rw [Real.log_div (by positivity) (by norm_num), Real.log_pow, ← hL_def] at h
        norm_num1 at h; linarith only [h]
      have hlB : Real.log B ≤ 60 * L + Real.log 2 := by
        have h := Real.log_le_log (by exact_mod_cast (hA1.trans hAB))
          (Nat.floor_le (show 0 ≤ 2 * s ^ 60 by positivity))
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, ← hL_def] at h
        norm_num1 at h; linarith only [h]
      dsimp only [Q_cap]
      rw [windowPrimes_eq_primesLE_sdiff_nat]
      linarith [mertensFirst_general_block hA1 hAB]
    have hsum := (sum_le_sum hrow).trans
      ((mul_sum _ _ _).symm.trans_le (mul_le_mul_of_nonneg_left hmert_cap (by positivity)))
    refine hsum.trans ?_
    rw [hlogT]
    have hCcol_nonneg : 0 ≤ C_col := by
      dsimp [C_col]
      linarith [Real.log_pos (show (1 : ℝ) < 16 / 9 by norm_num), hlog2_pos, hmert_nonneg]
    have hCcap_L : 2 * Real.log 2 + mertensBlockGapConst ≤ (1 / 2000000) * L := by
      dsimp [C_col] at hCcol_nonneg; linarith only [hL_col, hCcol_nonneg]
    calc (2 * T / (60 * 59 * L ^ 2)) * (2 * Real.log 2 + mertensBlockGapConst)
        ≤ (2 * T / (60 * 59 * L ^ 2)) * ((1 / 2000000) * L) :=
          mul_le_mul_of_nonneg_left hCcap_L (by positivity)
      _ = (240 / (60 * 59 * 2000000 : ℝ)) * (T / (120 * L)) := by field_simp; ring
      _ ≤ (1 / 2000) * (T / (120 * L)) :=
          mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ = (1 / 2000) * T / (120 * L) := by ring
  have hcov_r : ((fibrePos X b).card : ℝ) ≤
      (∑ q ∈ Q_col, ((windowPrimes (T / q) (2 * T / q)).card : ℝ)) +
      (∑ i ∈ range 14, ∑ q ∈ Q_slice i, ((windowPrimes (T / q) (2 * T / q)).card : ℝ)) +
      (∑ q ∈ Q_cap, ((windowPrimes (T / q) (2 * T / q)).card : ℝ)) := by
    exact_mod_cast hpos_cover
  dsimp only [Q_slice] at hcov_r
  have h1000 : (1 / 2000 : ℝ) * T / Real.log T + (1 / 2000) * T / Real.log T =
      (1 / 1000) * T / Real.log T := by ring
  linarith only [hcov_r, hcol_hi, hcap_hi, h1000]

private lemma root_pos_upper_14slice (X b q₁ q₂ : ℕ) (T s A_up : ℝ)
    (hX1 : 1 ≤ X) (hq₁ : q₁.Prime) (hq₂ : q₂.Prime) (hb_eq : b = q₁ * q₂)
    (hT_def : T = (X : ℝ) / b) (hs4 : 4 ≤ s) (hs120 : s ^ (120 : ℕ) = T)
    (hAs : 2 * A_up ≤ s)
    (hL_mert : 40000 * (Real.log 2 + mertensBlockGapConst) ≤ Real.log s)
    (hL_col : 2000000 * ((Real.log (16 / 9) + Real.log 2 + mertensBlockGapConst) +
      2 * Real.log 2 + mertensBlockGapConst) ≤ Real.log s)
    (hq₂_lo : (9 / 16) * s ^ 32 < (q₂ : ℝ))
    (hup : ∀ R : ℝ, A_up ≤ R → ∀ u v : ℝ, R ≤ u → u ≤ v → v ≤ 2 * R →
      R / Real.log R ^ (0 : ℝ) ≤ v - u →
      ((windowPrimes u v).card : ℝ) ≤ (1 + 1 / 2000) * (v - u) / Real.log R) :
    ((fibrePos X b).card : ℝ) ≤ (1025 / 1000) * T / Real.log T := by
  have hs2 : 2 ≤ s := by linarith only [hs4]
  have hs1 : 1 ≤ s := by linarith only [hs4]
  have hs0 : 0 < s := by linarith only [hs4]
  have hb_pos : 0 < b := hb_eq ▸ Nat.mul_pos hq₁.pos hq₂.pos
  have hb_r : (0 : ℝ) < b := by exact_mod_cast hb_pos
  have hT_pos : 0 < T := by rw [hT_def]; exact div_pos (by exact_mod_cast hX1) hb_r
  obtain ⟨L, hL_def⟩ : ∃ L : ℝ, L = Real.log s := ⟨_, rfl⟩
  rw [← hL_def] at hL_mert
  have hL0 : 0 < L := by rw [hL_def]; exact Real.log_pos (by linarith only [hs4])
  have hlogT : Real.log T = 120 * L := by
    rw [← hs120, Real.log_pow, ← hL_def]; norm_num
  have hlogT_pos : 0 < Real.log T := by rw [hlogT]; positivity
  have hcov_cap := root_pos_upper_collar_and_cap X b q₁ q₂ T s A_up hX1 hq₁ hq₂ hb_eq hT_def
    hs4 hs120 hAs (by rwa [← hL_def]) hL_col hq₂_lo hup
  let Q_slice : ℕ → Finset ℕ := fun i => windowPrimes (s ^ (32 + 2 * i)) (s ^ (34 + 2 * i))
  have hslice_hi : ∀ i ∈ range 14,
      ∑ q ∈ Q_slice i, ((windowPrimes (T / q) (2 * T / q)).card : ℝ) ≤
        (1001 / 1000) * ((60 : ℝ) / ((16 + (i : ℝ)) * (44 - (i : ℝ)))) * (T / Real.log T) := by
    intro i hi
    have hi_lt : i < 14 := mem_range.mp hi
    have hi_r : (i : ℝ) ≤ 13 := by exact_mod_cast (Nat.lt_succ_iff.mp hi_lt)
    have hden_pos : 0 < (16 + (i : ℝ)) * (44 - (i : ℝ)) := by nlinarith only [hi_r]
    have h60_i : (34 + 2 * (i : ℝ)) * L ≤ 60 * L :=
      mul_le_mul_of_nonneg_right (by linarith only [hi_r]) hL0.le
    have h32_60_i : (32 + 2 * (i : ℝ)) * L ≤ 60 * L :=
      mul_le_mul_of_nonneg_right (by linarith only [hi_r]) hL0.le
    have hrow_hi : ∀ q ∈ Q_slice i,
        ((windowPrimes (T / q) (2 * T / q)).card : ℝ) ≤
          (2001 / 2000) * (T / (4 * ((16 + (i : ℝ)) * (44 - (i : ℝ))) * L ^ 2)) *
            (Real.log (q : ℝ) / (q : ℝ)) := by
      intro q hq
      obtain ⟨hqp, hq_lo, hq_hi⟩ := (mem_windowPrimes (by positivity) (by positivity)).mp hq
      have hq_0 : (0 : ℝ) < q := by exact_mod_cast hqp.pos
      have hlq_pos : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hqp.one_lt)
      have hq_s60 : (q : ℝ) ≤ s ^ 60 := hq_hi.trans (pow_le_pow_right₀ hs1 (by omega))
      have hTq_ge_s : s ≤ T / q := by
        rw [le_div_iff₀ hq_0, ← hs120]
        calc s * q ≤ s ^ 60 * s ^ 60 :=
              mul_le_mul (by simpa only [pow_one] using pow_le_pow_right₀ hs1 (by decide : 1 ≤ 60))
                hq_s60 (by positivity) (by positivity)
          _ = s ^ 120 := by ring
      have hlq_lo : (32 + 2 * (i : ℝ)) * L ≤ Real.log (q : ℝ) := by
        have h := Real.log_le_log (by positivity) hq_lo.le
        rw [Real.log_pow, ← hL_def] at h; push_cast at h; exact h
      have hlq_hi : Real.log (q : ℝ) ≤ (34 + 2 * (i : ℝ)) * L := by
        have h := Real.log_le_log hq_0 hq_hi
        rw [Real.log_pow, ← hL_def] at h; push_cast at h; exact h
      have hlq_60 : Real.log (q : ℝ) ≤ 60 * L := hlq_hi.trans h60_i
      have hlTq_pos : 0 < Real.log (T / q) := by
        rw [Real.log_div hT_pos.ne' hq_0.ne', hlogT]; linarith only [hlq_60, hL0]
      have hconc : 4 * ((16 + (i : ℝ)) * (44 - (i : ℝ))) * L ^ 2 ≤
          Real.log (q : ℝ) * Real.log (T / q) := by
        rw [Real.log_div hT_pos.ne' hq_0.ne', hlogT]
        have hdiff : Real.log (q : ℝ) * (120 * L - Real.log (q : ℝ)) -
            4 * ((16 + (i : ℝ)) * (44 - (i : ℝ))) * L ^ 2 =
          (Real.log (q : ℝ) - (32 + 2 * (i : ℝ)) * L) *
            (120 * L - Real.log (q : ℝ) - (32 + 2 * (i : ℝ)) * L) := by ring
        have hf1 : 0 ≤ Real.log (q : ℝ) - (32 + 2 * (i : ℝ)) * L := by linarith only [hlq_lo]
        have hf2 : 0 ≤ 120 * L - Real.log (q : ℝ) - (32 + 2 * (i : ℝ)) * L := by
          linarith only [hlq_60, h32_60_i]
        linarith only [hdiff, mul_nonneg hf1 hf2]
      have hdiff : 2 * T / (q : ℝ) - T / q = T / q := by ring
      have hw := hup (T / q) ((by linarith only [hAs, hs0] : A_up ≤ s).trans hTq_ge_s)
        (T / q) (2 * T / q) le_rfl (by rw [mul_div_assoc]; linarith only [div_pos hT_pos hq_0])
        (by rw [mul_div_assoc]) (by rw [Real.rpow_zero, div_one, hdiff])
      rw [hdiff] at hw
      refine hw.trans ?_
      have heq1 : (1 + 1 / 2000) * (T / q) / Real.log (T / q) =
          ((2001 / 2000) * T * Real.log (q : ℝ)) /
            ((q : ℝ) * (Real.log (q : ℝ) * Real.log (T / q))) := by
        field_simp; ring
      have heq2 : (2001 / 2000) * (T / (4 * ((16 + (i : ℝ)) * (44 - (i : ℝ))) * L ^ 2)) *
          (Real.log (q : ℝ) / (q : ℝ)) =
          ((2001 / 2000) * T * Real.log (q : ℝ)) /
            ((q : ℝ) * (4 * ((16 + (i : ℝ)) * (44 - (i : ℝ))) * L ^ 2)) := by
        field_simp
      rw [heq1, heq2]
      exact div_le_div_of_nonneg_left (by positivity)
        (mul_pos hq_0 (mul_pos (mul_pos (by norm_num) hden_pos) (sq_pos_of_pos hL0)))
        (mul_le_mul_of_nonneg_left hconc hq_0.le)
    have hmert := (mertens_power_band_bounds hs2 (by omega : 1 ≤ 32 + 2 * i)
      (by omega : 32 + 2 * i ≤ 34 + 2 * i)).2
    have hdiff_k : ((34 + 2 * i : ℕ) : ℝ) - ((32 + 2 * i : ℕ) : ℝ) = 2 := by push_cast; ring
    rw [hdiff_k, ← hL_def] at hmert
    have hmert_hi : ∑ q ∈ Q_slice i, Real.log (q : ℝ) / (q : ℝ) ≤ (20001 / 20000) * (2 * L) := by
      linarith only [hmert, hL_mert, hL0]
    have hsum_step := (sum_le_sum hrow_hi).trans
      ((mul_sum _ _ _).symm.trans_le
        (mul_le_mul_of_nonneg_left hmert_hi
          (mul_nonneg (by positivity)
            (div_nonneg hT_pos.le (mul_nonneg (mul_nonneg (by norm_num) hden_pos.le) (sq_nonneg L))))))
    refine hsum_step.trans ?_
    rw [hlogT]
    have hnum_rat : (2001 / 2000 : ℝ) * (20001 / 20000) ≤ 1001 / 1000 := by norm_num
    have hident : (2001 / 2000 : ℝ) *
        (T / (4 * ((16 + (i : ℝ)) * (44 - (i : ℝ))) * L ^ 2)) *
        ((20001 / 20000) * (2 * L)) =
        ((2001 / 2000) * (20001 / 20000)) *
          (((60 : ℝ) / ((16 + (i : ℝ)) * (44 - (i : ℝ)))) * (T / (120 * L))) := by
      field_simp; ring
    rw [hident, mul_assoc (1001 / 1000 : ℝ)]
    exact mul_le_mul_of_nonneg_right hnum_rat
      (mul_nonneg (div_nonneg (by norm_num) hden_pos.le)
        (div_nonneg hT_pos.le (mul_nonneg (by norm_num) hL0.le)))
  have hsum14 := sum_le_sum hslice_hi
  simp only [mul_assoc, ← mul_sum, ← sum_mul] at hsum14
  have h14_bound : (∑ i ∈ range 14, ∑ q ∈ Q_slice i,
      ((windowPrimes (T / q) (2 * T / q)).card : ℝ)) ≤ (1024 / 1000) * T / Real.log T := by
    refine hsum14.trans ?_
    calc (1001 / 1000 : ℝ) *
          ((∑ i ∈ range 14, (60 : ℝ) / ((16 + (i : ℝ)) * (44 - (i : ℝ)))) *
            (T / Real.log T))
        ≤ (1001 / 1000) * ((1022 / 1000) * (T / Real.log T)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right upper_fourteen_slice_sum_le
              (div_nonneg hT_pos.le hlogT_pos.le))
            (by norm_num)
      _ ≤ (1024 / 1000) * T / Real.log T := by
          rw [mul_div_assoc, ← mul_assoc]
          exact mul_le_mul_of_nonneg_right (by norm_num) (div_nonneg hT_pos.le hlogT_pos.le)
  have hcomb : (1 / 1000 : ℝ) * T / Real.log T + (1024 / 1000) * T / Real.log T =
      (1025 / 1000) * T / Real.log T := by ring
  dsimp only [Q_slice] at h14_bound
  linarith only [hcov_cap, h14_bound, hcomb]

/-- **Threshold-4/15 positive-surplus bounds on a root cofactor `b`**:
for sufficiently large `s = (X / b)^{1/120}` and any squarefree `b = q₁ * q₂` (`q₁ < q₂` primes)
satisfying `(9 / 16) * s³² < q₂ ≤ s³²`, the ordered fibre `F_X(b)` has strict positive surplus
`(1 / 1000) * T_b / log T_b ≤ #fibrePos(X, b) - #fibreNeg(X, b) ≤ (27 / 1000) * T_b / log T_b`. -/
theorem eventually_root_positive_surplus_bounds :
    ∃ S₀ : ℝ, 4 ≤ S₀ ∧ ∀ {X b q₁ q₂ : ℕ}, 1 ≤ X → q₁.Prime → q₂.Prime → q₁ < q₂ →
      b = q₁ * q₂ →
      let T : ℝ := (X : ℝ) / b
      let s : ℝ := T ^ (1 / 120 : ℝ)
      S₀ ≤ s →
      (9 / 16) * s ^ 32 < (q₂ : ℝ) → (q₂ : ℝ) ≤ s ^ 32 →
      (fibreNeg X b).card ≤ (fibrePos X b).card ∧
      (1 / 1000) * T / Real.log T ≤ ((fibrePos X b).card : ℝ) - ((fibreNeg X b).card : ℝ) ∧
      ((fibrePos X b).card : ℝ) - ((fibreNeg X b).card : ℝ) ≤ (27 / 1000) * T / Real.log T := by
  obtain ⟨A_up, _, hup⟩ := exists_card_windowPrimes_le (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2000)
  obtain ⟨H_lo, _, hlo⟩ := exists_card_windowPrimes_div_ge (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2000)
  let C_mert : ℝ := Real.log 2 + mertensBlockGapConst
  let C_col : ℝ := Real.log (16 / 9) + Real.log 2 + mertensBlockGapConst
  have hev : ∀ᶠ s : ℝ in atTop,
      4 ≤ s ∧ 2 * A_up ≤ s ∧ H_lo ≤ s ∧
      max (40000 * C_mert) (2000000 * (C_col + 2 * Real.log 2 + mertensBlockGapConst)) ≤
        Real.log s :=
    (eventually_ge_atTop 4).and ((eventually_ge_atTop _).and ((eventually_ge_atTop _).and
      (Real.tendsto_log_atTop.eventually_ge_atTop _)))
  obtain ⟨S₀, hS₀⟩ := eventually_atTop.mp hev
  refine ⟨max 4 S₀, le_max_left _ _,
    fun {X b q₁ q₂} hX1 hq₁ hq₂ hq₁₂ hb_eq hs hq₂_lo hq₂_hi => ?_⟩
  let T : ℝ := (X : ℝ) / b
  let s : ℝ := T ^ (1 / 120 : ℝ)
  obtain ⟨hs4, hAs, hHs, hLmax⟩ := hS₀ s ((le_max_right _ _).trans hs)
  have hs1 : 1 ≤ s := by linarith only [hs4]
  have hs0 : 0 < s := by linarith only [hs4]
  have hb_pos : 0 < b := hb_eq ▸ Nat.mul_pos hq₁.pos hq₂.pos
  have hb_r : (0 : ℝ) < b := by exact_mod_cast hb_pos
  have hT_pos : 0 < T := div_pos (by exact_mod_cast hX1) hb_r
  have hs120 : s ^ (120 : ℕ) = T := by
    rw [show s = T ^ (1 / 120 : ℝ) from rfl, ← Real.rpow_natCast, ← Real.rpow_mul hT_pos.le]
    norm_num
  have hlogT : Real.log T = 120 * Real.log s := by
    rw [← hs120, Real.log_pow]; norm_num
  have hlogT_pos : 0 < Real.log T := by
    rw [hlogT]; exact mul_pos (by norm_num) (Real.log_pos (by linarith only [hs4]))
  have hL_mert : 40000 * C_mert ≤ Real.log s := (le_max_left _ _).trans hLmax
  have hL_col : 2000000 * (C_col + 2 * Real.log 2 + mertensBlockGapConst) ≤ Real.log s :=
    (le_max_right _ _).trans hLmax
  have hmert_nonneg : 0 ≤ mertensBlockGapConst := by
    have h := mertensFirst_general_block (A := 1) (B := 1) le_rfl le_rfl
    simp at h; linarith
  have hlog2_L : 40000 * Real.log 2 ≤ Real.log s := by
    dsimp [C_mert] at hL_mert; linarith
  have hsq_b : Squarefree b := by
    rw [hb_eq]
    exact Nat.squarefree_mul_iff.mpr ⟨(Nat.coprime_primes hq₁ hq₂).mpr hq₁₂.ne,
      Irreducible.squarefree hq₁, Irreducible.squarefree hq₂⟩
  have htop_b : ∀ {p : ℕ}, q₂ < p → ∀ d ∈ b.primeFactors, d < p := by
    intro p hp d hd
    rw [hb_eq, Nat.primeFactors_mul hq₁.ne_zero hq₂.ne_zero, hq₁.primeFactors, hq₂.primeFactors] at hd
    rcases mem_union.mp hd with h1 | h2
    · rw [mem_singleton.mp h1]; exact hq₁₂.trans hp
    · rw [mem_singleton.mp h2]; exact hp
  have heven_b : Even b.primeFactors.card := by
    have ht : ∀ d ∈ q₁.primeFactors, d < q₂ := fun d hd =>
      (Nat.le_of_dvd hq₁.pos (Nat.dvd_of_mem_primeFactors hd)).trans_lt hq₁₂
    rw [hb_eq, card_primeFactors_mul_larger_prime hq₁.ne_zero hq₂ ht, hq₁.primeFactors, card_singleton]
    exact ⟨1, rfl⟩
  have hq₂_lt_T : (q₂ : ℝ) < T := by
    have : s ^ 32 < s ^ 120 := pow_lt_pow_right₀ (by linarith only [hs4]) (by decide)
    linarith [hs120]
  have hneg_card : (fibreNeg X b).card = (windowPrimes T (2 * T)).card := by
    have himg : (windowPrimes T (2 * T)).image (b * ·) = fibreNeg X b := by
      ext n; simp only [mem_image]
      constructor
      · rintro ⟨p, hp_win, rfl⟩
        obtain ⟨hpp, hp_lo, hp_hi⟩ := (mem_windowPrimes hT_pos.le (by positivity)).mp hp_win
        have htp := htop_b (by exact_mod_cast hq₂_lt_T.trans hp_lo)
        have hμ : μ (b * p) = -1 := by
          rw [moebius_mul_larger_prime hb_pos.ne' hpp htp,
            moebius_eq_neg_one_pow_omega hsq_b, heven_b.neg_one_pow]
        have hIoc : b * p ∈ Ioc X (2 * X) := by
          dsimp [T] at hp_lo hp_hi
          rw [div_lt_iff₀ hb_r, mul_comm] at hp_lo
          rw [mul_div_assoc', le_div_iff₀ hb_r, mul_comm] at hp_hi
          exact mem_Ioc.mpr ⟨by exact_mod_cast (show (X : ℝ) < ((b * p : ℕ) : ℝ) by push_cast; linarith),
            by exact_mod_cast (show ((b * p : ℕ) : ℝ) ≤ (2 * X : ℕ) by push_cast; linarith)⟩
        refine mem_filter.mpr ⟨mem_filter.mpr ⟨hIoc, hμ⟩, ?_⟩
        rw [evenPrefixCofactor_eq_maxPrimeStem_of_neg hμ]
        exact maxPrimeStem_mul_prime hb_pos.ne' hpp htp
      · intro hn
        obtain ⟨_, _, p, hpp, hna, _⟩ := mem_fibreNeg_structure hX1 hn
        obtain ⟨hn_lo, hn_hi⟩ := mem_Ioc.mp (mem_filter.mp (mem_filter.mp hn).1).1
        refine ⟨p, (mem_windowPrimes hT_pos.le (by positivity)).mpr ⟨hpp, ?_, ?_⟩, hna.symm⟩
        · dsimp [T]; rw [div_lt_iff₀ hb_r, mul_comm]
          exact_mod_cast (hna ▸ hn_lo : X < b * p)
        · dsimp [T]; rw [mul_div_assoc', le_div_iff₀ hb_r, mul_comm]
          exact_mod_cast (hna ▸ hn_hi : b * p ≤ 2 * X)
    rw [← himg, card_image_of_injOn fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_left hb_pos h]
  have hs_le_T : s ≤ T := by
    rw [← hs120]; simpa only [pow_one] using pow_le_pow_right₀ hs1 (by decide : 1 ≤ 120)
  have hneg_hi : ((fibreNeg X b).card : ℝ) ≤ (2001 / 2000) * T / Real.log T := by
    rw [hneg_card]
    have hdiff_T : 2 * T - T = T := by ring
    have h := hup T ((by linarith : A_up ≤ s).trans hs_le_T) T (2 * T) le_rfl
      (by linarith) le_rfl (by rw [Real.rpow_zero, div_one, hdiff_T])
    linarith [show (1 + 1 / 2000) * (2 * T - T) / Real.log T = (2001 / 2000) * T / Real.log T by ring]
  have hneg_lo : (999 / 1000) * T / Real.log T ≤ ((fibreNeg X b).card : ℝ) := by
    rw [hneg_card]
    have hdiff_2T : 4 * T - 2 * T = 2 * T := by ring
    have h := hlo (2 * T) (hHs.trans (hs_le_T.trans (by linarith))) 2 (by norm_num) (by norm_num)
      (2 * T) (4 * T) le_rfl (by linarith) (by linarith) (by rw [Real.rpow_zero, div_one, hdiff_2T])
    have hd1 : 2 * T / 2 = T := by ring
    have hd2 : 4 * T / 2 = 2 * T := by ring
    rw [hd1, hd2] at h
    have hlog2T : Real.log (2 * T) ≤ (20001 / 20000) * Real.log T := by
      rw [Real.log_mul (by norm_num) hT_pos.ne', hlogT]
      linarith [hlog2_L]
    calc (999 / 1000) * T / Real.log T
        ≤ (1999 / 2000) * T / ((20001 / 20000) * Real.log T) := by
          rw [div_le_div_iff₀ hlogT_pos (by positivity)]
          nlinarith [mul_pos hT_pos hlogT_pos]
      _ ≤ (1999 / 2000) * T / Real.log (2 * T) :=
          div_le_div_of_nonneg_left (by positivity) (Real.log_pos (by linarith)) hlog2T
      _ = (1 - 1 / 2000) * (4 * T - 2 * T) / (2 * Real.log (2 * T)) := by ring
      _ ≤ _ := h
  have hpos_lo := root_pos_lower_14slice X b q₁ q₂ T s H_lo hX1 hq₁ hq₂ hq₁₂ hb_eq rfl hs4 hs120
    hHs hL_mert hq₂_hi hlo
  have hpos_hi := root_pos_upper_14slice X b q₁ q₂ T s A_up hX1 hq₁ hq₂ hb_eq rfl hs4 hs120
    hAs hL_mert hL_col hq₂_lo hup
  have hdiff_lo : (1 / 1000) * T / Real.log T ≤
      ((fibrePos X b).card : ℝ) - ((fibreNeg X b).card : ℝ) := by
    have : (1 / 1000 : ℝ) * T / Real.log T ≤
        (10017 / 10000) * T / Real.log T - (2001 / 2000) * T / Real.log T := by
      rw [show (10017 / 10000 : ℝ) * T / Real.log T - (2001 / 2000) * T / Real.log T =
        (12 / 10000) * (T / Real.log T) by ring, mul_div_assoc]
      exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    linarith [hpos_lo, hneg_hi]
  have hdiff_hi : ((fibrePos X b).card : ℝ) - ((fibreNeg X b).card : ℝ) ≤
      (27 / 1000) * T / Real.log T := by
    have : (1025 / 1000 : ℝ) * T / Real.log T - (999 / 1000) * T / Real.log T ≤
        (27 / 1000) * T / Real.log T := by
      rw [show (1025 / 1000 : ℝ) * T / Real.log T - (999 / 1000) * T / Real.log T =
        (26 / 1000) * (T / Real.log T) by ring, mul_div_assoc]
      exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    linarith [hpos_hi, hneg_lo]
  have hcard_le : (fibreNeg X b).card ≤ (fibrePos X b).card := by
    have hpos_diff : 0 < ((fibrePos X b).card : ℝ) - ((fibreNeg X b).card : ℝ) :=
      lt_of_lt_of_le (by positivity) hdiff_lo
    exact_mod_cast (by linarith : ((fibreNeg X b).card : ℝ) ≤ (fibrePos X b).card)
  exact ⟨hcard_le, hdiff_lo, hdiff_hi⟩

/-! ### 4. Child empty-positive supply, balanced cluster involution, and `X^{113/180}` saving -/

private lemma balanced_child_elem_props (X b q₁ q₂ : ℕ) (T s : ℝ)
    (P₁_b P₂_b : Finset ℕ)
    (hX1 : 1 ≤ X) (hq₁_pr : q₁.Prime) (hq₂_pr : q₂.Prime) (hq₁₂ : q₁ < q₂)
    (hb_eq : b = q₁ * q₂)
    (hT_def : T = (X : ℝ) / b) (hs4 : 4 ≤ s) (hs120 : s ^ (120 : ℕ) = T)
    (hq₂_s_hi : (q₂ : ℝ) ≤ s ^ 32)
    (hP₁_def : P₁_b = windowPrimes (s ^ 32) (s ^ 35))
    (hP₂_def : P₂_b = windowPrimes (s ^ 35) (s ^ 42)) :
    ∀ p₁ ∈ P₁_b, ∀ p₂ ∈ P₂_b,
      (b * p₁ * p₂).primeFactors.card = 4 ∧
      maxPrimeStem (b * p₁ * p₂) = b * p₁ ∧
      maxPrimeStem (maxPrimeStem (b * p₁ * p₂)) = b ∧
      fibrePos X (b * p₁ * p₂) = ∅ ∧
      fibreNeg X (b * p₁ * p₂) =
        (windowPrimes (T / (p₁ * p₂)) (2 * T / (p₁ * p₂))).image ((b * p₁ * p₂) * ·) ∧
      (fibreNeg X (b * p₁ * p₂)).card ≤ ⌊2 * s ^ 53⌋₊ := by
  have hs2 : 2 ≤ s := by linarith only [hs4]
  have hs1 : 1 ≤ s := by linarith only [hs4]
  have hs0 : 0 < s := by linarith only [hs4]
  have hb_pos : 0 < b := hb_eq ▸ Nat.mul_pos hq₁_pr.pos hq₂_pr.pos
  have hb_r : (0 : ℝ) < b := by exact_mod_cast hb_pos
  have hT_pos : 0 < T := by rw [hT_def]; exact div_pos (by exact_mod_cast hX1) hb_r
  have hb_card2 : b.primeFactors.card = 2 := by
    have ht : ∀ d ∈ q₁.primeFactors, d < q₂ := fun d hd =>
      (Nat.le_of_dvd hq₁_pr.pos (Nat.dvd_of_mem_primeFactors hd)).trans_lt hq₁₂
    rw [hb_eq, card_primeFactors_mul_larger_prime hq₁_pr.ne_zero hq₂_pr ht,
      hq₁_pr.primeFactors, card_singleton]
  have hsq_b : Squarefree b := by
    rw [hb_eq]
    exact Nat.squarefree_mul_iff.mpr ⟨(Nat.coprime_primes hq₁_pr hq₂_pr).mpr hq₁₂.ne,
      Irreducible.squarefree hq₁_pr, Irreducible.squarefree hq₂_pr⟩
  have htop_b : ∀ {p : ℕ}, q₂ < p → ∀ d ∈ b.primeFactors, d < p := by
    intro p hp d hd
    rw [hb_eq, Nat.primeFactors_mul hq₁_pr.ne_zero hq₂_pr.ne_zero,
      hq₁_pr.primeFactors, hq₂_pr.primeFactors] at hd
    rcases mem_union.mp hd with h1 | h2
    · rw [mem_singleton.mp h1]; exact hq₁₂.trans hp
    · rw [mem_singleton.mp h2]; exact hp
  intro p₁ hp₁P p₂ hp₂P
  rw [hP₁_def] at hp₁P; rw [hP₂_def] at hp₂P
  obtain ⟨hp₁_pr, hp₁_lo, hp₁_hi⟩ := (mem_windowPrimes (by positivity) (by positivity)).mp hp₁P
  obtain ⟨hp₂_pr, hp₂_lo, hp₂_hi⟩ := (mem_windowPrimes (by positivity) (by positivity)).mp hp₂P
  have hq₂_lt_p₁ : q₂ < p₁ := by exact_mod_cast hq₂_s_hi.trans_lt hp₁_lo
  have hp₁_lt_p₂ : p₁ < p₂ := by exact_mod_cast hp₁_hi.trans_lt hp₂_lo
  have htop_p₁ := htop_b hq₂_lt_p₁
  have htop_p₂ := primeFactors_lt_of_mul_prime hb_pos.ne' hp₁_pr hp₁_lt_p₂ htop_p₁
  have hbp₁_pos : 0 < b * p₁ := Nat.mul_pos hb_pos hp₁_pr.pos
  have ha_pos : 0 < b * p₁ * p₂ := Nat.mul_pos hbp₁_pos hp₂_pr.pos
  have ha_r : (0 : ℝ) < (b * p₁ * p₂ : ℕ) := by exact_mod_cast ha_pos
  have hp₁₂_r : (0 : ℝ) < (p₁ : ℝ) * p₂ := by exact_mod_cast Nat.mul_pos hp₁_pr.pos hp₂_pr.pos
  have ha_card : (b * p₁ * p₂).primeFactors.card = 4 := by
    rw [card_primeFactors_mul_larger_prime hbp₁_pos.ne' hp₂_pr htop_p₂,
      card_primeFactors_mul_larger_prime hb_pos.ne' hp₁_pr htop_p₁, hb_card2]
  obtain ⟨hs1_st, hs2_st⟩ := maxPrimeStem_mul_pair hb_pos.ne' hp₁_pr hp₂_pr hp₁_lt_p₂ htop_p₁
  have hmul_assoc : b * p₁ * p₂ = b * (p₁ * p₂) := Nat.mul_assoc b p₁ p₂
  have hpos_emp : fibrePos X (b * p₁ * p₂) = ∅ := by
    apply fibrePos_eq_empty_of_primeFactor_sq_ge hX1
      (Nat.mem_primeFactors.mpr ⟨hp₂_pr, dvd_mul_left p₂ (b * p₁), ha_pos.ne'⟩)
    have hp₂_3 : s ^ 105 ≤ (p₂ : ℝ) ^ 3 := by
      have : (s ^ 35) ^ 3 = s ^ 105 := by ring
      rw [← this]; exact pow_le_pow_left₀ (by positivity) hp₂_lo.le 3
    have hgt : 2 * (X : ℝ) ≤ ((b * p₁ * p₂ * p₂ ^ 2 : ℕ) : ℝ) := by
      push_cast
      have hX_eq : (X : ℝ) = b * s ^ 120 := by
        rw [hs120, hT_def]; exact (mul_div_cancel₀ _ hb_r.ne').symm
      have hs137 : 2 * s ^ 120 ≤ s ^ 32 * s ^ 105 := by
        calc 2 * s ^ 120 ≤ s * s ^ 120 := mul_le_mul_of_nonneg_right hs2 (by positivity)
          _ = s ^ 121 := by ring
          _ ≤ s ^ 137 := pow_le_pow_right₀ hs1 (by decide)
          _ = s ^ 32 * s ^ 105 := by ring
      calc 2 * (X : ℝ) = b * (2 * s ^ 120) := by rw [hX_eq]; ring
        _ ≤ b * (s ^ 32 * s ^ 105) := mul_le_mul_of_nonneg_left hs137 (by positivity)
        _ ≤ b * ((p₁ : ℝ) * (p₂ : ℝ) ^ 3) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul hp₁_lo.le hp₂_3 (by positivity) (by positivity)) (by positivity)
        _ = b * p₁ * p₂ * (p₂ : ℝ) ^ 2 := by ring
    exact_mod_cast hgt
  have hp₂_lt_Ta : (p₂ : ℝ) < T / ((p₁ : ℝ) * p₂) := by
    rw [lt_div_iff₀ hp₁₂_r, ← hs120]
    calc (p₂ : ℝ) * (p₁ * p₂) ≤ s ^ 42 * (s ^ 35 * s ^ 42) :=
          mul_le_mul hp₂_hi (mul_le_mul hp₁_hi hp₂_hi (by positivity) (by positivity))
            (by positivity) (by positivity)
      _ = s ^ 119 := by ring
      _ < s ^ 120 := pow_lt_pow_right₀ (by linarith only [hs4]) (by decide)
  have hsq_a : Squarefree (b * p₁ * p₂) := by
    have hnd₁ : ¬ p₁ ∣ b := fun hd =>
      (htop_p₁ p₁ (Nat.mem_primeFactors.mpr ⟨hp₁_pr, hd, hb_pos.ne'⟩)).false
    have hsq₁ : Squarefree (b * p₁) :=
      Nat.squarefree_mul_iff.mpr
        ⟨(hp₁_pr.coprime_iff_not_dvd.mpr hnd₁).symm, hsq_b, Irreducible.squarefree hp₁_pr⟩
    have hnd₂ : ¬ p₂ ∣ b * p₁ := fun hd =>
      (htop_p₂ p₂ (Nat.mem_primeFactors.mpr ⟨hp₂_pr, hd, hbp₁_pos.ne'⟩)).false
    exact Nat.squarefree_mul_iff.mpr
      ⟨(hp₂_pr.coprime_iff_not_dvd.mpr hnd₂).symm, hsq₁, Irreducible.squarefree hp₂_pr⟩
  have heven_a : Even (b * p₁ * p₂).primeFactors.card := by rw [ha_card]; exact ⟨2, rfl⟩
  have hTa_eq : T / ((p₁ : ℝ) * p₂) = (X : ℝ) / (b * p₁ * p₂ : ℕ) := by
    rw [hT_def]; push_cast; rw [div_div, mul_assoc]
  have h2Ta_eq : 2 * T / ((p₁ : ℝ) * p₂) = 2 * ((X : ℝ) / (b * p₁ * p₂ : ℕ)) := by
    rw [← hTa_eq]; ring
  have hneg_eq : fibreNeg X (b * p₁ * p₂) =
      (windowPrimes (T / (p₁ * p₂)) (2 * T / (p₁ * p₂))).image ((b * p₁ * p₂) * ·) := by
    ext n; simp only [mem_image]
    constructor
    · intro hn
      obtain ⟨_, _, p₃, hp₃_pr, hna, _⟩ := mem_fibreNeg_structure hX1 hn
      obtain ⟨hn_lo, hn_hi⟩ := mem_Ioc.mp (mem_filter.mp (mem_filter.mp hn).1).1
      refine ⟨p₃, (mem_windowPrimes (by positivity) (by positivity)).mpr ⟨hp₃_pr, ?_, ?_⟩, hna.symm⟩
      · rw [hTa_eq, div_lt_iff₀ ha_r]
        exact_mod_cast (show X < p₃ * (b * p₁ * p₂) by rw [mul_comm, ← hna]; exact hn_lo)
      · rw [h2Ta_eq, mul_div_assoc', le_div_iff₀ ha_r]
        exact_mod_cast (show p₃ * (b * p₁ * p₂) ≤ 2 * X by rw [mul_comm, ← hna]; exact hn_hi)
    · rintro ⟨p₃, hp₃_win, rfl⟩
      obtain ⟨hp₃_pr, hp₃_lo, hp₃_hi⟩ := (mem_windowPrimes (by positivity) (by positivity)).mp hp₃_win
      have hp₂_lt_p₃ : p₂ < p₃ := by exact_mod_cast hp₂_lt_Ta.trans hp₃_lo
      have htop_p₃ := primeFactors_lt_of_mul_prime hbp₁_pos.ne' hp₂_pr hp₂_lt_p₃ htop_p₂
      have hμ_n : μ (b * p₁ * p₂ * p₃) = -1 := by
        rw [moebius_mul_larger_prime ha_pos.ne' hp₃_pr htop_p₃,
          moebius_eq_neg_one_pow_omega hsq_a, heven_a.neg_one_pow]
      have hIoc_n : b * p₁ * p₂ * p₃ ∈ Ioc X (2 * X) := by
        rw [hTa_eq, div_lt_iff₀ ha_r] at hp₃_lo
        rw [h2Ta_eq, mul_div_assoc', le_div_iff₀ ha_r] at hp₃_hi
        have hcomm : ((b * p₁ * p₂ * p₃ : ℕ) : ℝ) = (p₃ : ℝ) * (b * p₁ * p₂ : ℕ) := by
          push_cast; ring
        exact mem_Ioc.mpr ⟨by exact_mod_cast (show (X : ℝ) < ((b * p₁ * p₂ * p₃ : ℕ) : ℝ) by rw [hcomm]; exact hp₃_lo),
          by exact_mod_cast (show ((b * p₁ * p₂ * p₃ : ℕ) : ℝ) ≤ (2 * X : ℕ) by
            rw [hcomm, Nat.cast_mul 2 X, Nat.cast_ofNat]; exact hp₃_hi)⟩
      refine mem_filter.mpr ⟨mem_filter.mpr ⟨hIoc_n, hμ_n⟩, ?_⟩
      rw [evenPrefixCofactor_eq_maxPrimeStem_of_neg hμ_n]
      exact maxPrimeStem_mul_prime ha_pos.ne' hp₃_pr htop_p₃
  have hcard_neg_le : (fibreNeg X (b * p₁ * p₂)).card ≤ ⌊2 * s ^ 53⌋₊ := by
    rw [hneg_eq, card_image_of_injOn fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_left ha_pos h]
    have hsub : windowPrimes (T / (p₁ * p₂)) (2 * T / (p₁ * p₂)) ⊆ Icc 1 ⌊2 * s ^ 53⌋₊ := by
      intro p₃ hp₃
      obtain ⟨hp₃_pr, _, hp₃_hi⟩ := (mem_windowPrimes (by positivity) (by positivity)).mp hp₃
      have h2T_hi : 2 * T / ((p₁ : ℝ) * p₂) ≤ 2 * s ^ 53 := by
        rw [div_le_iff₀ hp₁₂_r, ← hs120]
        calc 2 * s ^ 120 = 2 * s ^ 53 * (s ^ 32 * s ^ 35) := by ring
          _ ≤ 2 * s ^ 53 * ((p₁ : ℝ) * p₂) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul hp₁_lo.le hp₂_lo.le (by positivity) (by positivity)) (by positivity)
      exact mem_Icc.mpr ⟨hp₃_pr.pos, Nat.le_floor (hp₃_hi.trans h2T_hi)⟩
    simpa using card_le_card hsub
  exact ⟨ha_card, hmul_assoc.symm ▸ hs1_st, hmul_assoc.symm ▸ hs2_st,
    hpos_emp, hneg_eq, hcard_neg_le⟩

private lemma balanced_child_pool_bounds (X b q₁ q₂ : ℕ) (z T s H_lo : ℝ)
    (P₁_b P₂_b : Finset ℕ)
    (hX1 : 1 ≤ X) (hq₁_pr : q₁.Prime) (hq₂_pr : q₂.Prime) (hq₁₂ : q₁ < q₂)
    (hb_eq : b = q₁ * q₂) (hz4 : 4 ≤ z)
    (hT_def : T = (X : ℝ) / b) (hs4 : 4 ≤ s) (hs120 : s ^ (120 : ℕ) = T)
    (hzs : z ≤ s) (hz_Hlo : H_lo ≤ z)
    (hLz_mert : 20 * (Real.log 2 + mertensBlockGapConst) ≤ Real.log z)
    (hq₂_s_hi : (q₂ : ℝ) ≤ s ^ 32)
    (hneg_le_pos : (fibreNeg X b).card ≤ (fibrePos X b).card)
    (hsurp_hi : ((fibrePos X b).card : ℝ) - ((fibreNeg X b).card : ℝ) ≤ (27 / 1000) * T / Real.log T)
    (hP₁_def : P₁_b = windowPrimes (s ^ 32) (s ^ 35))
    (hP₂_def : P₂_b = windowPrimes (s ^ 35) (s ^ 42))
    (hpool_eq : balancedChildPool X b = (P₁_b ×ˢ P₂_b).image fun p₁₂ => b * p₁₂.1 * p₁₂.2)
    (hlo_2000 : ∀ R : ℝ, H_lo ≤ R → ∀ q : ℝ, 2 ≤ q → q ≤ 5 → ∀ u v : ℝ,
      R ≤ u → u ≤ v → v ≤ 2 * R → R / Real.log R ^ (0 : ℝ) ≤ v - u →
      (1 - 1 / 2000) * (v - u) / (q * Real.log R) ≤ ((windowPrimes (u / q) (v / q)).card : ℝ)) :
    (∀ p₁ ∈ P₁_b, ∀ p₂ ∈ P₂_b,
      (b * p₁ * p₂).primeFactors.card = 4 ∧
      maxPrimeStem (b * p₁ * p₂) = b * p₁ ∧
      maxPrimeStem (maxPrimeStem (b * p₁ * p₂)) = b ∧
      fibrePos X (b * p₁ * p₂) = ∅ ∧
      fibreNeg X (b * p₁ * p₂) =
        (windowPrimes (T / (p₁ * p₂)) (2 * T / (p₁ * p₂))).image ((b * p₁ * p₂) * ·) ∧
      (fibreNeg X (b * p₁ * p₂)).card ≤ ⌊2 * s ^ 53⌋₊) ∧
    (fibrePos X b).card - (fibreNeg X b).card ≤
      ∑ a ∈ balancedChildPool X b, (fibreNeg X a).card := by
  have hz0 : 0 < z := by linarith only [hz4]
  have hs2 : 2 ≤ s := by linarith only [hs4]
  have hs1 : 1 ≤ s := by linarith only [hs4]
  have hs0 : 0 < s := by linarith only [hs4]
  have hb_pos : 0 < b := hb_eq ▸ Nat.mul_pos hq₁_pr.pos hq₂_pr.pos
  have hb_r : (0 : ℝ) < b := by exact_mod_cast hb_pos
  have hT_pos : 0 < T := by rw [hT_def]; exact div_pos (by exact_mod_cast hX1) hb_r
  have hchild_elem := balanced_child_elem_props X b q₁ q₂ T s P₁_b P₂_b hX1 hq₁_pr hq₂_pr hq₁₂
    hb_eq hT_def hs4 hs120 hq₂_s_hi hP₁_def hP₂_def
  have hinj_pool : Set.InjOn (fun p₁₂ : ℕ × ℕ => b * p₁₂.1 * p₁₂.2) ↑(P₁_b ×ˢ P₂_b) := by
    rintro ⟨p₁, p₂⟩ hp₁₂ ⟨p₁', p₂'⟩ hp₁₂' heq
    dsimp only at heq
    obtain ⟨hp₁, hp₂⟩ := mem_product.mp hp₁₂
    obtain ⟨hp₁', hp₂'⟩ := mem_product.mp hp₁₂'
    dsimp only at hp₁ hp₂ hp₁' hp₂'
    have hs₁ := (hchild_elem p₁ hp₁ p₂ hp₂).2.1
    have hs₁' := (hchild_elem p₁' hp₁' p₂' hp₂').2.1
    have hbp₁_eq : b * p₁ = b * p₁' := hs₁.symm.trans ((congrArg maxPrimeStem heq).trans hs₁')
    have hp₁_eq : p₁ = p₁' := Nat.eq_of_mul_eq_mul_left hb_pos hbp₁_eq
    subst hp₁_eq
    rw [hP₁_def] at hp₁
    have hp₁_pos := ((mem_windowPrimes (by positivity) (by positivity)).mp hp₁).1.pos
    exact Prod.ext rfl (Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hb_pos hp₁_pos) heq)
  refine ⟨hchild_elem, ?_⟩
  obtain ⟨L, hL_def⟩ : ∃ L : ℝ, L = Real.log s := ⟨_, rfl⟩
  have hLs_ge : Real.log z ≤ L := by rw [hL_def]; exact Real.log_le_log hz0 hzs
  have hL0 : 0 < L := by rw [hL_def]; exact Real.log_pos (by linarith only [hs4])
  have hLmert_s : 20 * (Real.log 2 + mertensBlockGapConst) ≤ L := hLz_mert.trans hLs_ge
  have hlogT : Real.log T = 120 * L := by rw [← hs120, Real.log_pow, ← hL_def]; norm_num
  have hlogT_pos : 0 < Real.log T := by rw [hlogT]; exact mul_pos (by norm_num) hL0
  have hP₁_rec : (29 / 350 : ℝ) ≤ ∑ p₁ ∈ P₁_b, 1 / (p₁ : ℝ) := by
    have hm := (mertens_power_band_bounds hs2 (by decide : 1 ≤ 32) (by decide : 32 ≤ 35)).1
    rw [← hP₁_def, ← hL_def] at hm; norm_num1 at hm
    have h1 : (29 / 10) * L ≤ ∑ p₁ ∈ P₁_b, Real.log (p₁ : ℝ) / (p₁ : ℝ) := by linarith
    have h2 : ∑ p₁ ∈ P₁_b, Real.log (p₁ : ℝ) / (p₁ : ℝ) ≤
        (35 * L) * ∑ p₁ ∈ P₁_b, 1 / (p₁ : ℝ) := by
      rw [mul_sum]
      refine sum_le_sum fun p₁ hp₁ => ?_
      rw [hP₁_def] at hp₁
      obtain ⟨hp₁_pr, _, hp₁_hi⟩ := (mem_windowPrimes (by positivity) (by positivity)).mp hp₁
      have hp₁_0 : (0 : ℝ) < p₁ := by exact_mod_cast hp₁_pr.pos
      have hl := Real.log_le_log hp₁_0 hp₁_hi
      rw [Real.log_pow, ← hL_def] at hl; norm_num1 at hl
      simpa only [div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_right hl (inv_nonneg.mpr hp₁_0.le)
    apply le_of_mul_le_mul_left _ (show (0 : ℝ) < 35 * L by positivity)
    linarith [h1.trans h2]
  have hP₂_rec : (23 / 140 : ℝ) ≤ ∑ p₂ ∈ P₂_b, 1 / (p₂ : ℝ) := by
    have hm := (mertens_power_band_bounds hs2 (by decide : 1 ≤ 35) (by decide : 35 ≤ 42)).1
    rw [← hP₂_def, ← hL_def] at hm; norm_num1 at hm
    have h1 : (69 / 10) * L ≤ ∑ p₂ ∈ P₂_b, Real.log (p₂ : ℝ) / (p₂ : ℝ) := by linarith
    have h2 : ∑ p₂ ∈ P₂_b, Real.log (p₂ : ℝ) / (p₂ : ℝ) ≤
        (42 * L) * ∑ p₂ ∈ P₂_b, 1 / (p₂ : ℝ) := by
      rw [mul_sum]
      refine sum_le_sum fun p₂ hp₂ => ?_
      rw [hP₂_def] at hp₂
      obtain ⟨hp₂_pr, _, hp₂_hi⟩ := (mem_windowPrimes (by positivity) (by positivity)).mp hp₂
      have hp₂_0 : (0 : ℝ) < p₂ := by exact_mod_cast hp₂_pr.pos
      have hl := Real.log_le_log hp₂_0 hp₂_hi
      rw [Real.log_pow, ← hL_def] at hl; norm_num1 at hl
      simpa only [div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_right hl (inv_nonneg.mpr hp₂_0.le)
    apply le_of_mul_le_mul_left _ (show (0 : ℝ) < 42 * L by positivity)
    linarith [h1.trans h2]
  have hterm_lo : ∀ p₁₂ ∈ P₁_b ×ˢ P₂_b,
      ((1999 / 2000) * (120 / 54) * (T / Real.log T)) *
        ((1 / (p₁₂.1 : ℝ)) * (1 / (p₁₂.2 : ℝ))) ≤
          ((fibreNeg X (b * p₁₂.1 * p₁₂.2)).card : ℝ) := by
    rintro ⟨p₁, p₂⟩ hp₁₂
    dsimp only
    obtain ⟨hp₁P, hp₂P⟩ := mem_product.mp hp₁₂
    dsimp only at hp₁P hp₂P
    have hneg_eq := (hchild_elem p₁ hp₁P p₂ hp₂P).2.2.2.2.1
    rw [hP₁_def] at hp₁P; rw [hP₂_def] at hp₂P
    obtain ⟨hp₁_pr, hp₁_lo, hp₁_hi⟩ := (mem_windowPrimes (by positivity) (by positivity)).mp hp₁P
    obtain ⟨hp₂_pr, hp₂_lo, hp₂_hi⟩ := (mem_windowPrimes (by positivity) (by positivity)).mp hp₂P
    have ha_pos : 0 < b * p₁ * p₂ := Nat.mul_pos (Nat.mul_pos hb_pos hp₁_pr.pos) hp₂_pr.pos
    have hcard_eq : (fibreNeg X (b * p₁ * p₂)).card =
        (windowPrimes (T / (p₁ * p₂)) (2 * T / (p₁ * p₂))).card := by
      rw [hneg_eq, card_image_of_injOn fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_left ha_pos h]
    rw [hcard_eq]
    have hp₁₂_0 : (0 : ℝ) < (p₁ : ℝ) * p₂ := by exact_mod_cast Nat.mul_pos hp₁_pr.pos hp₂_pr.pos
    have hTa_ge_s : s ≤ T / ((p₁ : ℝ) * p₂) := by
      rw [le_div_iff₀ hp₁₂_0, ← hs120]
      calc s * ((p₁ : ℝ) * p₂) ≤ s * (s ^ 35 * s ^ 42) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul hp₁_hi hp₂_hi (by positivity) (by positivity)) hs0.le
        _ = s ^ 78 := by ring
        _ ≤ s ^ 120 := pow_le_pow_right₀ hs1 (by decide)
    have h2Ta_le : 2 * (T / ((p₁ : ℝ) * p₂)) ≤ 2 * s ^ 53 := by
      rw [mul_div_assoc', div_le_iff₀ hp₁₂_0, ← hs120]
      calc 2 * s ^ 120 = 2 * s ^ 53 * (s ^ 32 * s ^ 35) := by ring
        _ ≤ 2 * s ^ 53 * ((p₁ : ℝ) * p₂) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul hp₁_lo.le hp₂_lo.le (by positivity) (by positivity)) (by positivity)
    have hl2Ta : Real.log (2 * (T / ((p₁ : ℝ) * p₂))) ≤ 54 * L := by
      have hmert_nn : 0 ≤ mertensBlockGapConst := by
        have hm0 := mertensFirst_general_block (A := 1) (B := 1) le_rfl le_rfl
        simp at hm0; linarith only [hm0]
      calc Real.log (2 * (T / ((p₁ : ℝ) * p₂)))
          ≤ Real.log (2 * s ^ 53) := Real.log_le_log (by positivity) h2Ta_le
        _ = Real.log 2 + 53 * L := by
            rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, ← hL_def]
            norm_num
        _ ≤ 54 * L := by linarith only [hLmert_s, hmert_nn, hL0]
    have hdiff_2Ta : 4 * (T / ((p₁ : ℝ) * p₂)) - 2 * (T / ((p₁ : ℝ) * p₂)) =
        2 * (T / ((p₁ : ℝ) * p₂)) := by ring
    have hw := hlo_2000 (2 * (T / ((p₁ : ℝ) * p₂)))
      ((hz_Hlo.trans hzs).trans (hTa_ge_s.trans (by linarith only [hs0, hTa_ge_s])))
      2 (by norm_num) (by norm_num)
      (2 * (T / ((p₁ : ℝ) * p₂))) (4 * (T / ((p₁ : ℝ) * p₂)))
      le_rfl (by linarith [div_pos hT_pos hp₁₂_0]) (by linarith [div_pos hT_pos hp₁₂_0])
      (by rw [Real.rpow_zero, div_one, hdiff_2Ta])
    have hd1 : 2 * (T / ((p₁ : ℝ) * p₂)) / 2 = T / ((p₁ : ℝ) * p₂) := by ring
    have hd2 : 4 * (T / ((p₁ : ℝ) * p₂)) / 2 = 2 * T / ((p₁ : ℝ) * p₂) := by ring
    rw [hd1, hd2] at hw
    refine le_trans ?_ hw
    rw [hlogT]
    have hlhs_eq : ((1999 / 2000) * (120 / 54) * (T / (120 * L))) *
        ((1 / (p₁ : ℝ)) * (1 / (p₂ : ℝ))) =
        (1999 / 2000) * (T / ((p₁ : ℝ) * p₂)) / (54 * L) := by field_simp
    have hrhs_eq : (1 - 1 / 2000) *
        (4 * (T / ((p₁ : ℝ) * p₂)) - 2 * (T / ((p₁ : ℝ) * p₂))) /
        (2 * Real.log (2 * (T / ((p₁ : ℝ) * p₂)))) =
        (1999 / 2000) * (T / ((p₁ : ℝ) * p₂)) /
          Real.log (2 * (T / ((p₁ : ℝ) * p₂))) := by ring
    rw [hlhs_eq, hrhs_eq]
    exact div_le_div_of_nonneg_left (by positivity)
      (Real.log_pos (by linarith only [hs4, hTa_ge_s])) hl2Ta
  have hsum_r : (27 / 1000) * T / Real.log T ≤
      (∑ a ∈ balancedChildPool X b, (fibreNeg X a).card : ℝ) := by
    rw [hpool_eq, sum_image hinj_pool]
    have hstep := sum_le_sum hterm_lo
    rw [← mul_sum, sum_product] at hstep
    dsimp only at hstep
    rw [← sum_mul_sum] at hstep
    refine le_trans ?_ hstep
    have hprod_rec : (29 / 350 : ℝ) * (23 / 140) ≤
        (∑ p₁ ∈ P₁_b, 1 / (p₁ : ℝ)) * (∑ p₂ ∈ P₂_b, 1 / (p₂ : ℝ)) :=
      mul_le_mul hP₁_rec hP₂_rec (by norm_num)
        (sum_nonneg fun _ _ => div_nonneg zero_le_one (Nat.cast_nonneg _))
    have hrat : (27 / 1000 : ℝ) ≤
        (1999 / 2000) * (120 / 54) * ((29 / 350) * (23 / 140)) := by norm_num
    calc (27 / 1000) * T / Real.log T
        = (27 / 1000) * (T / Real.log T) := by ring
      _ ≤ ((1999 / 2000) * (120 / 54) * ((29 / 350) * (23 / 140))) * (T / Real.log T) :=
          mul_le_mul_of_nonneg_right hrat (div_nonneg hT_pos.le hlogT_pos.le)
      _ = ((1999 / 2000) * (120 / 54) * (T / Real.log T)) *
            ((29 / 350) * (23 / 140)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hprod_rec
          (mul_nonneg (by norm_num) (div_nonneg hT_pos.le hlogT_pos.le))
  have hdiff_cast : (((fibrePos X b).card - (fibreNeg X b).card : ℕ) : ℝ) =
      ((fibrePos X b).card : ℝ) - ((fibreNeg X b).card : ℝ) :=
    Nat.cast_sub hneg_le_pos
  exact_mod_cast (hdiff_cast ▸ hsurp_hi.trans hsum_r)

private theorem mem_cofactorCubeRow_of_factors {X c p₂ p₃ : ℕ} {u_c : ℝ}
    (huc : u_c = ((X : ℝ) / c) ^ (1 / 6 : ℝ))
    (hp₂ : p₂ ∈ windowPrimes (u_c ^ 2 / 2) (2 * u_c ^ 3))
    (hp₃ : p₃ ∈ windowPrimes ((X : ℝ) / c / p₂) (2 * (X : ℝ) / c / p₂))
    (hp₂_pr : p₂.Prime) (hp₃_pr : p₃.Prime) (hp₂₃ : p₂ < p₃)
    (htop : ∀ d ∈ c.primeFactors, d < p₂) :
    p₂ * p₃ ∈ cofactorCubeRow X c := by
  subst huc
  exact mem_filter.mpr ⟨mem_biUnion.mpr ⟨p₂, hp₂, mem_image.mpr ⟨p₃, hp₃, rfl⟩⟩,
    p₂, p₃, hp₂_pr, hp₃_pr, hp₂₃, rfl, htop⟩

private theorem cofactorCubeRow_subset_cubeBandProducts {X c : ℕ} {u_c : ℝ}
    (huc : u_c = ((X : ℝ) / c) ^ (1 / 6 : ℝ))
    (huc6 : (X : ℝ) / c = u_c ^ 6)
    (h2uc6 : 2 * (X : ℝ) / c = 2 * u_c ^ 6) :
    cofactorCubeRow X c ⊆ cubeBandProducts u_c (u_c ^ 6) (2 * u_c ^ 6) := by
  dsimp only [cofactorCubeRow]
  rw [← huc, huc6, h2uc6]
  exact filter_subset _ _

private lemma balanced_child_row_capacity (X b q₁ q₂ : ℕ) (z T s S_cap : ℝ)
    (P₁_b P₂_b N_child : Finset ℕ)
    (hX1 : 1 ≤ X) (hq₁_pr : q₁.Prime) (hq₂_pr : q₂.Prime) (hq₁₂ : q₁ < q₂)
    (hb_eq : b = q₁ * q₂)
    (hT_def : T = (X : ℝ) / b) (hs4 : 4 ≤ s) (hs120 : s ^ (120 : ℕ) = T)
    (hzs : z ≤ s) (hz_Scap : S_cap ^ 6 ≤ z)
    (hq₂_s_hi : (q₂ : ℝ) ≤ s ^ 32)
    (hP₁_def : P₁_b = windowPrimes (s ^ 32) (s ^ 35))
    (hP₂_def : P₂_b = windowPrimes (s ^ 35) (s ^ 42))
    (hpool_eq : balancedChildPool X b = (P₁_b ×ˢ P₂_b).image fun p₁₂ => b * p₁₂.1 * p₁₂.2)
    (hsel_sub : balancedChildSelection X b ⊆ balancedChildPool X b)
    (hN_def : N_child = (balancedChildSelection X b).biUnion (fibreNeg X))
    (hchild_elem : ∀ p₁ ∈ P₁_b, ∀ p₂ ∈ P₂_b,
      (b * p₁ * p₂).primeFactors.card = 4 ∧
      maxPrimeStem (b * p₁ * p₂) = b * p₁ ∧
      maxPrimeStem (maxPrimeStem (b * p₁ * p₂)) = b ∧
      fibrePos X (b * p₁ * p₂) = ∅ ∧
      fibreNeg X (b * p₁ * p₂) =
        (windowPrimes (T / (p₁ * p₂)) (2 * T / (p₁ * p₂))).image ((b * p₁ * p₂) * ·) ∧
      (fibreNeg X (b * p₁ * p₂)).card ≤ ⌊2 * s ^ 53⌋₊)
    (hS_cap : ∀ u : ℝ, S_cap ≤ u →
      10 * (cubeBandProducts u (u ^ 6) (2 * u ^ 6)).card ≤
        9 * (windowPrimes (u ^ 6) (2 * u ^ 6)).card) :
    let childRow : ℕ → Finset ℕ := fun p₁ =>
      N_child.filter fun n => maxPrimeStem (maxPrimeStem n) = b * p₁
    (∀ n ∈ N_child,
      ∃ p₁ ∈ P₁_b, ∃ p₂ ∈ P₂_b, ∃ p₃ : ℕ,
        p₃ ∈ windowPrimes (T / (p₁ * p₂)) (2 * T / (p₁ * p₂)) ∧
        n = b * p₁ * p₂ * p₃ ∧
        maxPrimeStem (maxPrimeStem n) = b * p₁ ∧
        p₂ * p₃ ∈ cofactorCubeRow X (b * p₁)) ∧
    P₁_b.biUnion childRow = N_child ∧
    (P₁_b : Set ℕ).PairwiseDisjoint childRow ∧
    ∀ p₁ ∈ P₁_b, (childRow p₁).card ≤
      (windowPrimes ((X : ℝ) / (b * p₁ : ℕ)) (2 * (X : ℝ) / (b * p₁ : ℕ))).card := by
  have hs1 : 1 ≤ s := by linarith only [hs4]
  have hs0 : 0 < s := by linarith only [hs4]
  have hb_pos : 0 < b := hb_eq ▸ Nat.mul_pos hq₁_pr.pos hq₂_pr.pos
  have hb_r : (0 : ℝ) < b := by exact_mod_cast hb_pos
  have hT_pos : 0 < T := by rw [hT_def]; exact div_pos (by exact_mod_cast hX1) hb_r
  have htop_b : ∀ {p : ℕ}, q₂ < p → ∀ d ∈ b.primeFactors, d < p := by
    intro p hp d hd
    rw [hb_eq, Nat.primeFactors_mul hq₁_pr.ne_zero hq₂_pr.ne_zero,
      hq₁_pr.primeFactors, hq₂_pr.primeFactors] at hd
    rcases mem_union.mp hd with h1 | h2
    · rw [mem_singleton.mp h1]; exact hq₁₂.trans hp
    · rw [mem_singleton.mp h2]; exact hp
  intro childRow
  let W_sup : ℕ → Finset ℕ := fun p₁ =>
    windowPrimes ((X : ℝ) / (b * p₁ : ℕ)) (2 * (X : ℝ) / (b * p₁ : ℕ))
  have hN_elem_decomp : ∀ n ∈ N_child,
      ∃ p₁ ∈ P₁_b, ∃ p₂ ∈ P₂_b, ∃ p₃ : ℕ,
        p₃ ∈ windowPrimes (T / (p₁ * p₂)) (2 * T / (p₁ * p₂)) ∧
        n = b * p₁ * p₂ * p₃ ∧
        maxPrimeStem (maxPrimeStem n) = b * p₁ ∧
        p₂ * p₃ ∈ cofactorCubeRow X (b * p₁) := by
    intro n hnC
    rw [hN_def] at hnC
    obtain ⟨a, haC, hna⟩ := mem_biUnion.mp hnC
    have hap := hsel_sub haC
    rw [hpool_eq] at hap
    obtain ⟨⟨p₁, p₂⟩, hp₁₂, rfl⟩ := mem_image.mp hap
    obtain ⟨hp₁P, hp₂P⟩ := mem_product.mp hp₁₂
    dsimp only at hp₁P hp₂P hna
    obtain ⟨_, _, _, _, hneg_eq_a, _⟩ := hchild_elem p₁ hp₁P p₂ hp₂P
    rw [hneg_eq_a] at hna
    obtain ⟨p₃, hp₃_win, rfl⟩ := mem_image.mp hna
    have hp₁W := hp₁P; rw [hP₁_def] at hp₁W
    have hp₂W := hp₂P; rw [hP₂_def] at hp₂W
    have hs_nn : 0 ≤ s := hs0.le
    obtain ⟨hp₁_pr, hp₁_lo, hp₁_hi⟩ :=
      (mem_windowPrimes (pow_nonneg hs_nn 32) (pow_nonneg hs_nn 35)).mp hp₁W
    obtain ⟨hp₂_pr, hp₂_lo, hp₂_hi⟩ :=
      (mem_windowPrimes (pow_nonneg hs_nn 35) (pow_nonneg hs_nn 42)).mp hp₂W
    obtain ⟨hp₃_pr, hp₃_lo, _⟩ :=
      (mem_windowPrimes
        (div_nonneg hT_pos.le (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
        (div_nonneg (mul_nonneg (by norm_num) hT_pos.le)
          (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))).mp hp₃_win
    have hq₂_lt_p₁ : q₂ < p₁ := by exact_mod_cast hq₂_s_hi.trans_lt hp₁_lo
    have hp₁_lt_p₂ : p₁ < p₂ := by exact_mod_cast hp₁_hi.trans_lt hp₂_lo
    have hp₂_lt_Ta : (p₂ : ℝ) < T / ((p₁ : ℝ) * p₂) := by
      rw [lt_div_iff₀ (by exact_mod_cast Nat.mul_pos hp₁_pr.pos hp₂_pr.pos), ← hs120]
      calc (p₂ : ℝ) * (p₁ * p₂) ≤ s ^ 42 * (s ^ 35 * s ^ 42) :=
            mul_le_mul hp₂_hi
              (mul_le_mul hp₁_hi hp₂_hi (Nat.cast_nonneg _) (pow_nonneg hs_nn 35))
              (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (pow_nonneg hs_nn 42)
        _ = s ^ 119 := by ring
        _ < s ^ 120 := pow_lt_pow_right₀ (by linarith only [hs4]) (by decide)
    have hp₂_lt_p₃ : p₂ < p₃ := by exact_mod_cast hp₂_lt_Ta.trans hp₃_lo
    have htop_p₁ := htop_b hq₂_lt_p₁
    have htop_p₂ := primeFactors_lt_of_mul_prime hb_pos.ne' hp₁_pr hp₁_lt_p₂ htop_p₁
    have hbp₁_pos : 0 < b * p₁ := Nat.mul_pos hb_pos hp₁_pr.pos
    have hss_n : maxPrimeStem (maxPrimeStem (b * p₁ * p₂ * p₃)) = b * p₁ := by
      rw [Nat.mul_assoc (b * p₁) p₂ p₃]
      exact (maxPrimeStem_mul_pair hbp₁_pos.ne' hp₂_pr hp₃_pr hp₂_lt_p₃ htop_p₂).2
    obtain ⟨u_c, huc_def⟩ : ∃ u_c : ℝ, u_c = ((X : ℝ) / (b * p₁ : ℕ)) ^ (1 / 6 : ℝ) := ⟨_, rfl⟩
    have hXbp₁_nn : 0 ≤ (X : ℝ) / (b * p₁ : ℕ) := div_nonneg (Nat.cast_nonneg X) (Nat.cast_nonneg _)
    have huc0 : 0 ≤ u_c := by rw [huc_def]; exact Real.rpow_nonneg hXbp₁_nn _
    have huc6 : u_c ^ 6 = (X : ℝ) / (b * p₁ : ℕ) := by
      rw [huc_def, ← Real.rpow_natCast, ← Real.rpow_mul hXbp₁_nn]; norm_num
    have huc6_eq : u_c ^ 6 = T / p₁ := by
      rw [huc6, hT_def]; push_cast; rw [div_div]
    have huc6_lo : s ^ 85 ≤ u_c ^ 6 := by
      rw [huc6_eq, le_div_iff₀ (by exact_mod_cast hp₁_pr.pos), ← hs120]
      calc s ^ 85 * p₁ ≤ s ^ 85 * s ^ 35 := mul_le_mul_of_nonneg_left hp₁_hi (pow_nonneg hs_nn 85)
        _ = s ^ 120 := by ring
    have huc6_hi : u_c ^ 6 < s ^ 88 := by
      rw [huc6_eq, div_lt_iff₀ (by exact_mod_cast hp₁_pr.pos), ← hs120]
      calc s ^ 120 = s ^ 88 * s ^ 32 := by ring
        _ < s ^ 88 * p₁ := mul_lt_mul_of_pos_left hp₁_lo (pow_pos hs0 88)
    have hp₂_uc_lo : u_c ^ 2 / 2 < (p₂ : ℝ) := by
      have huc2 : u_c ^ 2 < s ^ 35 := by
        apply (pow_lt_pow_iff_left₀ (sq_nonneg u_c) (pow_nonneg hs_nn 35) (by decide : 3 ≠ 0)).mp
        have h1 : (u_c ^ 2) ^ 3 = u_c ^ 6 := by ring
        have h2 : (s ^ 35) ^ 3 = s ^ 105 := by ring
        rw [h1, h2]
        exact huc6_hi.trans_le (pow_le_pow_right₀ hs1 (by decide))
      have hsq_nn := sq_nonneg u_c
      linarith only [hsq_nn, huc2, hp₂_lo]
    have hp₂_uc_hi : (p₂ : ℝ) ≤ 2 * u_c ^ 3 := by
      have hs42_uc3 : s ^ 42 ≤ u_c ^ 3 := by
        apply (pow_le_pow_iff_left₀ (pow_nonneg hs_nn 42) (pow_nonneg huc0 3) (by decide : 2 ≠ 0)).mp
        have h1 : (s ^ 42) ^ 2 = s ^ 84 := by ring
        have h2 : (u_c ^ 3) ^ 2 = u_c ^ 6 := by ring
        rw [h1, h2]
        exact (pow_le_pow_right₀ hs1 (by decide : 84 ≤ 85)).trans huc6_lo
      have h3_nn := pow_nonneg huc0 3
      linarith only [hp₂_hi, hs42_uc3, h3_nn]
    have hp₃_uc : p₃ ∈ windowPrimes ((X : ℝ) / (b * p₁ : ℕ) / p₂)
        (2 * (X : ℝ) / (b * p₁ : ℕ) / p₂) := by
      have hp₁_r0 : (0 : ℝ) < p₁ := by exact_mod_cast hp₁_pr.pos
      have hp₂_r0 : (0 : ℝ) < p₂ := by exact_mod_cast hp₂_pr.pos
      have heq1 : (X : ℝ) / (b * p₁ : ℕ) / p₂ = T / ((p₁ : ℝ) * p₂) := by
        rw [hT_def]; push_cast; field_simp
      have heq2 : 2 * (X : ℝ) / (b * p₁ : ℕ) / p₂ = 2 * T / ((p₁ : ℝ) * p₂) := by
        rw [hT_def]; push_cast; field_simp
      rw [heq1, heq2]
      exact hp₃_win
    have hw_cube : p₂ * p₃ ∈ cofactorCubeRow X (b * p₁) :=
      mem_cofactorCubeRow_of_factors huc_def
        ((mem_windowPrimes (div_nonneg (sq_nonneg u_c) (by norm_num))
          (mul_nonneg (by norm_num) (pow_nonneg huc0 3))).mpr ⟨hp₂_pr, hp₂_uc_lo, hp₂_uc_hi⟩)
        hp₃_uc hp₂_pr hp₃_pr hp₂_lt_p₃ htop_p₂
    exact ⟨p₁, hp₁P, p₂, hp₂P, p₃, hp₃_win, rfl, hss_n, hw_cube⟩
  have hN_part : P₁_b.biUnion childRow = N_child := by
    ext n; simp only [mem_biUnion, childRow, mem_filter]
    exact ⟨fun ⟨_, _, hn, _⟩ => hn, fun hn => by
      obtain ⟨p₁, hp₁P, _, _, _, _, _, hss, _⟩ := hN_elem_decomp n hn
      exact ⟨p₁, hp₁P, hn, hss⟩⟩
  have hdisj_childRow : (P₁_b : Set ℕ).PairwiseDisjoint childRow := by
    intro p₁ _ p₁' _ hne
    exact disjoint_left.mpr fun n hn₁ hn₂ => hne (Nat.eq_of_mul_eq_mul_left hb_pos
      ((mem_filter.mp hn₁).2.symm.trans (mem_filter.mp hn₂).2))
  have hrow_cap : ∀ p₁ ∈ P₁_b, (childRow p₁).card ≤ (W_sup p₁).card := by
    intro p₁ hp₁P
    rw [hP₁_def] at hp₁P
    obtain ⟨hp₁_pr, _, hp₁_hi⟩ :=
      (mem_windowPrimes (pow_nonneg hs0.le 32) (pow_nonneg hs0.le 35)).mp hp₁P
    have hbp₁_pos : 0 < b * p₁ := Nat.mul_pos hb_pos hp₁_pr.pos
    have hdiv_sub : (childRow p₁).image (· / (b * p₁)) ⊆ cofactorCubeRow X (b * p₁) := by
      intro w hw
      obtain ⟨n, hn_row, rfl⟩ := mem_image.mp hw
      obtain ⟨hnC, hss_eq⟩ := mem_filter.mp hn_row
      obtain ⟨p₁', _, p₂, _, p₃, _, rfl, hss', hw_cube⟩ := hN_elem_decomp n hnC
      have hp₁_eq : p₁' = p₁ := Nat.eq_of_mul_eq_mul_left hb_pos (hss'.symm.trans hss_eq)
      subst hp₁_eq
      rw [Nat.mul_assoc (b * p₁') p₂ p₃, mul_comm (b * p₁'), Nat.mul_div_cancel _ hbp₁_pos]
      exact hw_cube
    have hdiv_inj : Set.InjOn (· / (b * p₁)) ↑(childRow p₁) := by
      intro n₁ hn₁ n₂ hn₂ heq
      obtain ⟨p₁', _, p₂, _, p₃, _, rfl, hss₁, _⟩ := hN_elem_decomp n₁ (mem_filter.mp hn₁).1
      obtain ⟨p₁'', _, q₂', _, q₃', _, rfl, hss₂, _⟩ := hN_elem_decomp n₂ (mem_filter.mp hn₂).1
      have he₁ : p₁' = p₁ := Nat.eq_of_mul_eq_mul_left hb_pos (hss₁.symm.trans (mem_filter.mp hn₁).2)
      have he₂ : p₁'' = p₁ := Nat.eq_of_mul_eq_mul_left hb_pos (hss₂.symm.trans (mem_filter.mp hn₂).2)
      dsimp only at heq
      rw [he₁, he₂, Nat.mul_assoc (b * p₁) p₂ p₃, mul_comm (b * p₁), Nat.mul_div_cancel _ hbp₁_pos,
        Nat.mul_assoc (b * p₁) q₂' q₃', mul_comm (b * p₁), Nat.mul_div_cancel _ hbp₁_pos] at heq
      rw [he₁, he₂, Nat.mul_assoc (b * p₁) p₂ p₃, Nat.mul_assoc (b * p₁) q₂' q₃', heq]
    obtain ⟨u_c, huc_def⟩ : ∃ u_c : ℝ, u_c = ((X : ℝ) / (b * p₁ : ℕ)) ^ (1 / 6 : ℝ) := ⟨_, rfl⟩
    have hXbp₁_nn : 0 ≤ (X : ℝ) / (b * p₁ : ℕ) := div_nonneg (Nat.cast_nonneg X) (Nat.cast_nonneg _)
    have huc0 : 0 ≤ u_c := by rw [huc_def]; exact Real.rpow_nonneg hXbp₁_nn _
    have huc6 : u_c ^ 6 = (X : ℝ) / (b * p₁ : ℕ) := by
      rw [huc_def, ← Real.rpow_natCast, ← Real.rpow_mul hXbp₁_nn]; norm_num
    have huc_ge : S_cap ≤ u_c := by
      by_cases hS0 : S_cap ≤ 0
      · exact hS0.trans huc0
      · push Not at hS0
        apply (pow_le_pow_iff_left₀ hS0.le huc0 (by decide : 6 ≠ 0)).mp
        rw [huc6]
        have huc_s85 : s ^ 85 ≤ (X : ℝ) / (b * p₁ : ℕ) := by
          have heq_T : (X : ℝ) / (b * p₁ : ℕ) = T / p₁ := by
            rw [hT_def]; push_cast; rw [div_div]
          rw [heq_T, le_div_iff₀ (by exact_mod_cast hp₁_pr.pos), ← hs120]
          calc s ^ 85 * p₁ ≤ s ^ 85 * s ^ 35 := mul_le_mul_of_nonneg_left hp₁_hi (pow_nonneg hs0.le 85)
            _ = s ^ 120 := by ring
        have hz_s85 : z ≤ s ^ 85 :=
          hzs.trans (by simpa only [pow_one] using pow_le_pow_right₀ hs1 (by decide : 1 ≤ 85))
        exact hz_Scap.trans (hz_s85.trans huc_s85)
    have hcap9 := hS_cap u_c huc_ge
    have h2uc6 : 2 * (X : ℝ) / (b * p₁ : ℕ) = 2 * u_c ^ 6 := by rw [huc6]; ring
    have hsub_cube : cofactorCubeRow X (b * p₁) ⊆ cubeBandProducts u_c (u_c ^ 6) (2 * u_c ^ 6) :=
      cofactorCubeRow_subset_cubeBandProducts huc_def huc6.symm h2uc6
    have h10 : 10 * (childRow p₁).card ≤ 9 * (W_sup p₁).card := by
      rw [← card_image_of_injOn hdiv_inj]
      have h := (Nat.mul_le_mul_left 10 (card_le_card (hdiv_sub.trans hsub_cube))).trans hcap9
      dsimp only [W_sup]
      rwa [← h2uc6, huc6] at h
    omega
  exact ⟨hN_elem_decomp, hN_part, hdisj_childRow, hrow_cap⟩

private lemma balanced_cluster_involution_exists (X b q₁ q₂ : ℕ) (z T s S_cap : ℝ)
    (P₁_b P₂_b : Finset ℕ)
    (hX1 : 1 ≤ X) (hq₁_pr : q₁.Prime) (hq₂_pr : q₂.Prime) (hq₁₂ : q₁ < q₂)
    (hb_eq : b = q₁ * q₂)
    (hT_def : T = (X : ℝ) / b) (hs4 : 4 ≤ s) (hs120 : s ^ (120 : ℕ) = T)
    (hzs : z ≤ s) (hz_Scap : S_cap ^ 6 ≤ z)
    (hs53_hi : s ^ 53 ≤ 2 * z ^ 53)
    (hq₂_s_hi : (q₂ : ℝ) ≤ s ^ 32)
    (hneg_le_pos : (fibreNeg X b).card ≤ (fibrePos X b).card)
    (hP₁_def : P₁_b = windowPrimes (s ^ 32) (s ^ 35))
    (hP₂_def : P₂_b = windowPrimes (s ^ 35) (s ^ 42))
    (hpool_eq : balancedChildPool X b = (P₁_b ×ˢ P₂_b).image fun p₁₂ => b * p₁₂.1 * p₁₂.2)
    (hchild_elem : ∀ p₁ ∈ P₁_b, ∀ p₂ ∈ P₂_b,
      (b * p₁ * p₂).primeFactors.card = 4 ∧
      maxPrimeStem (b * p₁ * p₂) = b * p₁ ∧
      maxPrimeStem (maxPrimeStem (b * p₁ * p₂)) = b ∧
      fibrePos X (b * p₁ * p₂) = ∅ ∧
      fibreNeg X (b * p₁ * p₂) =
        (windowPrimes (T / (p₁ * p₂)) (2 * T / (p₁ * p₂))).image ((b * p₁ * p₂) * ·) ∧
      (fibreNeg X (b * p₁ * p₂)).card ≤ ⌊2 * s ^ 53⌋₊)
    (hpool_supply : (fibrePos X b).card - (fibreNeg X b).card ≤
      ∑ a ∈ balancedChildPool X b, (fibreNeg X a).card)
    (hS_cap : ∀ u : ℝ, S_cap ≤ u →
      10 * (cubeBandProducts u (u ^ 6) (2 * u ^ 6)).card ≤
        9 * (windowPrimes (u ^ 6) (2 * u ^ 6)).card) :
    (∀ a ∈ balancedChildSelection X b,
      a.primeFactors.card = 4 ∧ maxPrimeStem (maxPrimeStem a) = b ∧ fibrePos X a = ∅) ∧
    (∑ a ∈ balancedChildSelection X b, (fibreNeg X a).card) ≤
      (fibrePos X b).card - (fibreNeg X b).card ∧
    ∃ τ_b : FactorizationInvolution GlobalDyadicOneTwoRel
        (fibreUnion X (insert b (balancedChildSelection X b))),
      (τ_b.unmatchedSet.card : ℝ) ≤ 4 * z ^ 53 := by
  have hs0 : 0 < s := by linarith only [hs4]
  have hb_pos : 0 < b := hb_eq ▸ Nat.mul_pos hq₁_pr.pos hq₂_pr.pos
  have hb_r : (0 : ℝ) < b := by exact_mod_cast hb_pos
  have hT_pos : 0 < T := by rw [hT_def]; exact div_pos (by exact_mod_cast hX1) hb_r
  have hb_card2 : b.primeFactors.card = 2 := by
    have ht : ∀ d ∈ q₁.primeFactors, d < q₂ := fun d hd =>
      (Nat.le_of_dvd hq₁_pr.pos (Nat.dvd_of_mem_primeFactors hd)).trans_lt hq₁₂
    rw [hb_eq, card_primeFactors_mul_larger_prime hq₁_pr.ne_zero hq₂_pr ht,
      hq₁_pr.primeFactors, card_singleton]
  have hsq_b : Squarefree b := by
    rw [hb_eq]
    exact Nat.squarefree_mul_iff.mpr ⟨(Nat.coprime_primes hq₁_pr hq₂_pr).mpr hq₁₂.ne,
      Irreducible.squarefree hq₁_pr, Irreducible.squarefree hq₂_pr⟩
  have heven_b : Even b.primeFactors.card := by rw [hb_card2]; exact ⟨1, rfl⟩
  have htop_b : ∀ {p : ℕ}, q₂ < p → ∀ d ∈ b.primeFactors, d < p := by
    intro p hp d hd
    rw [hb_eq, Nat.primeFactors_mul hq₁_pr.ne_zero hq₂_pr.ne_zero,
      hq₁_pr.primeFactors, hq₂_pr.primeFactors] at hd
    rcases mem_union.mp hd with h1 | h2
    · rw [mem_singleton.mp h1]; exact hq₁₂.trans hp
    · rw [mem_singleton.mp h2]; exact hp
  have hgrain : ∀ a ∈ balancedChildPool X b, (fibreNeg X a).card ≤ ⌊2 * s ^ 53⌋₊ := by
    intro a ha
    rw [hpool_eq] at ha
    obtain ⟨⟨p₁, p₂⟩, hp₁₂, rfl⟩ := mem_image.mp ha
    exact (hchild_elem p₁ (mem_product.mp hp₁₂).1 p₂ (mem_product.mp hp₁₂).2).2.2.2.2.2
  obtain ⟨hsel_sub, hsel_le, hsel_ge⟩ := prefixSelect_spec hpool_supply hgrain
  change balancedChildSelection X b ⊆ balancedChildPool X b at hsel_sub
  change (∑ a ∈ balancedChildSelection X b, (fibreNeg X a).card) ≤
    (fibrePos X b).card - (fibreNeg X b).card at hsel_le
  change (fibrePos X b).card - (fibreNeg X b).card ≤
    (∑ a ∈ balancedChildSelection X b, (fibreNeg X a).card) + ⌊2 * s ^ 53⌋₊ at hsel_ge
  have hsel_props : ∀ a ∈ balancedChildSelection X b,
      a.primeFactors.card = 4 ∧ maxPrimeStem (maxPrimeStem a) = b ∧ fibrePos X a = ∅ := by
    intro a ha
    have hap := hsel_sub ha
    rw [hpool_eq] at hap
    obtain ⟨⟨p₁, p₂⟩, hp₁₂, rfl⟩ := mem_image.mp hap
    obtain ⟨hc4, _, hss, hemp, _, _⟩ :=
      hchild_elem p₁ (mem_product.mp hp₁₂).1 p₂ (mem_product.mp hp₁₂).2
    exact ⟨hc4, hss, hemp⟩
  have hb_not_sel : b ∉ balancedChildSelection X b := fun hb_in => by
    have := (hsel_props b hb_in).1; omega
  obtain ⟨C_sel, hC_sel⟩ : ∃ C_sel : Finset ℕ, C_sel = balancedChildSelection X b := ⟨_, rfl⟩
  obtain ⟨V_cl, hV_cl⟩ : ∃ V_cl : Finset ℕ, V_cl = fibreUnion X (insert b C_sel) := ⟨_, rfl⟩
  obtain ⟨N_child, hN_child⟩ : ∃ N_child : Finset ℕ, N_child = C_sel.biUnion (fibreNeg X) := ⟨_, rfl⟩
  have hdisj_fib_neg : (C_sel : Set ℕ).PairwiseDisjoint (fibreNeg X) :=
    fun _ _ _ _ hne => ((evenPrefixCofactor_complete_bipartite_fibres hX1).1 hne).2
  have hN_child_card : N_child.card = ∑ a ∈ C_sel, (fibreNeg X a).card := by
    rw [hN_child]; exact card_biUnion hdisj_fib_neg
  have hpos_cluster : posParity V_cl = fibrePos X b := by
    rw [hV_cl]
    ext m; simp only [posParity, fibreUnion, mem_filter, mem_biUnion, mem_insert, mem_union]
    constructor
    · rintro ⟨⟨a, rfl | haC, hp | hn⟩, _⟩
      · exact hp
      · have := (mem_filter.mp (mem_filter.mp hn).1).2; omega
      · rw [hC_sel] at haC; rw [(hsel_props a haC).2.2] at hp; exact False.elim (notMem_empty _ hp)
      · have := (mem_filter.mp (mem_filter.mp hn).1).2; omega
    · intro hp
      exact ⟨⟨b, Or.inl rfl, Or.inl hp⟩, (mem_filter.mp (mem_filter.mp hp).1).2⟩
  have hneg_cluster : negParity V_cl = fibreNeg X b ∪ N_child := by
    rw [hV_cl, hN_child]
    ext n; simp only [negParity, fibreUnion, mem_filter, mem_biUnion, mem_insert, mem_union]
    constructor
    · rintro ⟨⟨a, rfl | haC, hp | hn⟩, _⟩
      · have := (mem_filter.mp (mem_filter.mp hp).1).2; omega
      · exact Or.inl hn
      · have := (mem_filter.mp (mem_filter.mp hp).1).2; omega
      · exact Or.inr ⟨a, haC, hn⟩
    · rintro (hn | ⟨a, haC, hn⟩)
      · exact ⟨⟨b, Or.inl rfl, Or.inr hn⟩, (mem_filter.mp (mem_filter.mp hn).1).2⟩
      · exact ⟨⟨a, Or.inr haC, Or.inr hn⟩, (mem_filter.mp (mem_filter.mp hn).1).2⟩
  have hdisj_root_child_neg : Disjoint (fibreNeg X b) N_child := by
    rw [hN_child]
    refine disjoint_left.mpr fun n hnb hnC => ?_
    obtain ⟨a, haC, hna⟩ := mem_biUnion.mp hnC
    have hab : a = b := (mem_filter.mp hna).2.symm.trans (mem_filter.mp hnb).2
    rw [hC_sel, hab] at haC
    exact hb_not_sel haC
  have hsq_cluster : (squarefreeOf V_cl).card =
      (fibrePos X b).card + ((fibreNeg X b).card + N_child.card) := by
    rw [squarefreeOf_eq_posParity_union_negParity,
      card_union_of_disjoint (disjoint_posParity_negParity _),
      hpos_cluster, hneg_cluster, card_union_of_disjoint hdisj_root_child_neg]
  have hcap_call := balanced_child_row_capacity X b q₁ q₂ z T s S_cap P₁_b P₂_b N_child hX1
    hq₁_pr hq₂_pr hq₁₂ hb_eq hT_def hs4 hs120 hzs hz_Scap hq₂_s_hi hP₁_def hP₂_def hpool_eq
    hsel_sub (hN_child.trans (by rw [hC_sel])) hchild_elem hS_cap
  dsimp only at hcap_call
  obtain ⟨childRow, hchildRow⟩ : ∃ childRow : ℕ → Finset ℕ,
      childRow = fun p₁ => N_child.filter fun n => maxPrimeStem (maxPrimeStem n) = b * p₁ :=
    ⟨_, rfl⟩
  obtain ⟨W_sup, hW_sup⟩ : ∃ W_sup : ℕ → Finset ℕ,
      W_sup = fun p₁ => windowPrimes ((X : ℝ) / (b * p₁ : ℕ)) (2 * (X : ℝ) / (b * p₁ : ℕ)) :=
    ⟨_, rfl⟩
  rw [← hchildRow] at hcap_call
  obtain ⟨hN_elem_decomp, hN_part, hdisj_childRow, hrow_cap_raw⟩ := hcap_call
  have hrow_cap : ∀ p₁ ∈ P₁_b, (childRow p₁).card ≤ (W_sup p₁).card := fun p₁ hp₁ => by
    rw [hchildRow, hW_sup]; exact hrow_cap_raw p₁ hp₁
  obtain ⟨addrs, haddrs⟩ : ∃ addrs : Finset (ℕ × ℕ),
      addrs = P₁_b.biUnion fun p₁ => (range (childRow p₁).card).image fun i => (p₁, i) := ⟨_, rfl⟩
  have hmem_addrs : ∀ {p₁ i : ℕ}, (p₁, i) ∈ addrs ↔ p₁ ∈ P₁_b ∧ i < (childRow p₁).card := by
    intro p₁ i; rw [haddrs]
    simp only [mem_biUnion, mem_image, mem_range, Prod.mk.injEq]
    constructor
    · rintro ⟨p₁', hp₁', i', hi', rfl, rfl⟩; exact ⟨hp₁', hi'⟩
    · rintro ⟨hp₁, hi⟩; exact ⟨p₁, hp₁, i, hi, rfl, rfl⟩
  obtain ⟨f_ch, hf_ch⟩ : ∃ f_ch : ℕ × ℕ → ℕ,
      f_ch = fun a => (b * a.1) * finsetEntry (W_sup a.1) a.2 := ⟨_, rfl⟩
  obtain ⟨g_ch, hg_ch⟩ : ∃ g_ch : ℕ × ℕ → ℕ,
      g_ch = fun a => finsetEntry (childRow a.1) a.2 := ⟨_, rfl⟩
  have hch_spec : ∀ {p₁ i : ℕ}, (p₁, i) ∈ addrs →
      f_ch (p₁, i) ∈ fibrePos X b ∧
      maxPrimeStem (f_ch (p₁, i)) = b * p₁ ∧
      g_ch (p₁, i) ∈ N_child ∧
      GlobalDyadicOneTwoRel (f_ch (p₁, i)) (g_ch (p₁, i)) := by
    intro p₁ i ha
    obtain ⟨hp₁P, hi_lt⟩ := hmem_addrs.mp ha
    rw [hf_ch, hg_ch]; dsimp only
    have hi_sup : i < (W_sup p₁).card := hi_lt.trans_le (hrow_cap p₁ hp₁P)
    have hp₁W := hp₁P; rw [hP₁_def] at hp₁W
    have hs_nn : 0 ≤ s := hs0.le
    obtain ⟨hp₁_pr, hp₁_lo, hp₁_hi⟩ :=
      (mem_windowPrimes (pow_nonneg hs_nn 32) (pow_nonneg hs_nn 35)).mp hp₁W
    have hbp₁_pos : 0 < b * p₁ := Nat.mul_pos hb_pos hp₁_pr.pos
    have hbp₁_r : (0 : ℝ) < (b * p₁ : ℕ) := by exact_mod_cast hbp₁_pos
    have hp_win : finsetEntry (W_sup p₁) i ∈
        windowPrimes ((X : ℝ) / (b * p₁ : ℕ)) (2 * (X : ℝ) / (b * p₁ : ℕ)) := by
      rw [← congrFun hW_sup p₁]; exact finsetEntry_mem hi_sup
    obtain ⟨hpp, hp_lo, hp_hi⟩ :=
      (mem_windowPrimes (div_nonneg (Nat.cast_nonneg X) hbp₁_r.le)
        (div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg X)) hbp₁_r.le)).mp hp_win
    have hp₁_lt_p : p₁ < finsetEntry (W_sup p₁) i := by
      have hs85 : (p₁ : ℝ) < (X : ℝ) / (b * p₁ : ℕ) := by
        have heq_T : (X : ℝ) / (b * p₁ : ℕ) = T / p₁ := by
          rw [hT_def]; push_cast; rw [div_div]
        rw [heq_T, lt_div_iff₀ (by exact_mod_cast hp₁_pr.pos), ← hs120]
        calc (p₁ : ℝ) * p₁ ≤ s ^ 35 * s ^ 35 :=
              mul_le_mul hp₁_hi hp₁_hi (Nat.cast_nonneg _) (pow_nonneg hs_nn 35)
          _ = s ^ 70 := by ring
          _ < s ^ 120 := pow_lt_pow_right₀ (by linarith only [hs4]) (by decide)
      exact_mod_cast hs85.trans hp_lo
    have hq₂_lt_p₁ : q₂ < p₁ := by exact_mod_cast hq₂_s_hi.trans_lt hp₁_lo
    have htop_p₁ := htop_b hq₂_lt_p₁
    have htop_p := primeFactors_lt_of_mul_prime hb_pos.ne' hp₁_pr hp₁_lt_p htop_p₁
    have hμ_m : μ ((b * p₁) * finsetEntry (W_sup p₁) i) = 1 := by
      rw [moebius_mul_larger_prime hbp₁_pos.ne' hpp htop_p,
        moebius_mul_larger_prime hb_pos.ne' hp₁_pr htop_p₁,
        moebius_eq_neg_one_pow_omega hsq_b, heven_b.neg_one_pow]; norm_num
    have hIoc_m : (b * p₁) * finsetEntry (W_sup p₁) i ∈ Ioc X (2 * X) := by
      rw [div_lt_iff₀ hbp₁_r] at hp_lo
      rw [le_div_iff₀ hbp₁_r] at hp_hi
      have hcomm : (((b * p₁) * finsetEntry (W_sup p₁) i : ℕ) : ℝ) =
          (finsetEntry (W_sup p₁) i : ℝ) * (b * p₁ : ℕ) := by push_cast; ring
      exact mem_Ioc.mpr ⟨by exact_mod_cast (show (X : ℝ) < (((b * p₁) * finsetEntry (W_sup p₁) i : ℕ) : ℝ) by
          rw [hcomm]; exact hp_lo),
        by exact_mod_cast (show (((b * p₁) * finsetEntry (W_sup p₁) i : ℕ) : ℝ) ≤ (2 * X : ℕ) by
          rw [hcomm, Nat.cast_mul 2 X, Nat.cast_ofNat]; exact hp_hi)⟩
    have hm_fib : (b * p₁) * finsetEntry (W_sup p₁) i ∈ fibrePos X b := by
      rw [Nat.mul_assoc b p₁]
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨by rwa [← Nat.mul_assoc], by rwa [← Nat.mul_assoc]⟩,
        evenPrefixCofactor_mul_ordered_pair hb_pos.ne' heven_b hp₁_pr hpp hp₁_lt_p htop_p₁⟩
    have hn_row : finsetEntry (childRow p₁) i ∈
        N_child.filter (fun n => maxPrimeStem (maxPrimeStem n) = b * p₁) := by
      rw [← congrFun hchildRow p₁]; exact finsetEntry_mem hi_lt
    obtain ⟨hnC, hss_eq⟩ := mem_filter.mp hn_row
    obtain ⟨p₁', _, p₂, hp₂P, p₃, hp₃_win, hn_eq, hss', _⟩ := hN_elem_decomp _ hnC
    have hp₁'_eq : p₁' = p₁ := Nat.eq_of_mul_eq_mul_left hb_pos (hss'.symm.trans hss_eq)
    rw [hp₁'_eq] at hp₃_win hn_eq
    rw [hP₂_def] at hp₂P
    obtain ⟨hp₂_pr, _, hp₂_hi⟩ :=
      (mem_windowPrimes (pow_nonneg hs_nn 35) (pow_nonneg hs_nn 42)).mp hp₂P
    obtain ⟨hp₃_pr, hp₃_lo, _⟩ :=
      (mem_windowPrimes
        (div_nonneg hT_pos.le (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
        (div_nonneg (mul_nonneg (by norm_num) hT_pos.le)
          (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))).mp hp₃_win
    have hp₂_lt_p₃ : p₂ < p₃ := by
      have hp₂_lt_Ta : (p₂ : ℝ) < T / ((p₁ : ℝ) * p₂) := by
        rw [lt_div_iff₀ (by exact_mod_cast Nat.mul_pos hp₁_pr.pos hp₂_pr.pos), ← hs120]
        calc (p₂ : ℝ) * (p₁ * p₂) ≤ s ^ 42 * (s ^ 35 * s ^ 42) :=
              mul_le_mul hp₂_hi
                (mul_le_mul hp₁_hi hp₂_hi (Nat.cast_nonneg _) (pow_nonneg hs_nn 35))
                (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (pow_nonneg hs_nn 42)
          _ = s ^ 119 := by ring
          _ < s ^ 120 := pow_lt_pow_right₀ (by linarith only [hs4]) (by decide)
      exact_mod_cast hp₂_lt_Ta.trans hp₃_lo
    have hμ_n : μ (finsetEntry (childRow p₁) i) = -1 := by
      have hnC' := hnC; rw [hN_child] at hnC'
      obtain ⟨a, _, hna⟩ := mem_biUnion.mp hnC'
      exact (mem_filter.mp (mem_filter.mp hna).1).2
    refine ⟨hm_fib, maxPrimeStem_mul_prime hbp₁_pos.ne' hpp htop_p, hnC,
      ⟨squarefree_iff_moebius_ne_zero.mpr (by rw [hμ_m]; norm_num),
        squarefree_iff_moebius_ne_zero.mpr (by rw [hμ_n]; norm_num),
        by rw [hμ_m, hμ_n]; norm_num, b * p₁, finsetEntry (W_sup p₁) i, p₂, p₃,
        hpp, hp₂_pr, hp₃_pr, hp₂_lt_p₃,
        Or.inl ⟨rfl, hn_eq.trans (Nat.mul_assoc (b * p₁) p₂ p₃)⟩⟩⟩
  obtain ⟨unpair_ch, hunpair_ch_def⟩ : ∃ unpair_ch : ℕ → ℕ × ℕ,
      unpair_ch = fun m =>
        (maxPrimeStem m / b, finsetRank (W_sup (maxPrimeStem m / b)) (m / maxPrimeStem m)) :=
    ⟨_, rfl⟩
  have hunpair_ch : ∀ a ∈ addrs, unpair_ch (f_ch a) = a := by
    rintro ⟨p₁, i⟩ ha
    obtain ⟨hp₁P, hi_lt⟩ := hmem_addrs.mp ha
    have hstem := (hch_spec ha).2.1
    have hp₁W := hp₁P; rw [hP₁_def] at hp₁W
    have hp₁_pos := ((mem_windowPrimes (pow_nonneg hs0.le 32) (pow_nonneg hs0.le 35)).mp hp₁W).1.pos
    have hp₁_div : (b * p₁) / b = p₁ := by rw [mul_comm, Nat.mul_div_cancel _ hb_pos]
    have hm_div : f_ch (p₁, i) / (b * p₁) = finsetEntry (W_sup p₁) i := by
      rw [hf_ch]; dsimp only
      rw [mul_comm (b * p₁), Nat.mul_div_cancel _ (Nat.mul_pos hb_pos hp₁_pos)]
    rw [hunpair_ch_def]; dsimp only
    rw [hstem, hp₁_div, hm_div, finsetRank_entry (hi_lt.trans_le (hrow_cap p₁ hp₁P))]
  have hf_ch_inj : Set.InjOn f_ch ↑addrs := fun a₁ ha₁ a₂ ha₂ heq =>
    (hunpair_ch a₁ ha₁).symm.trans ((congrArg unpair_ch heq).trans (hunpair_ch a₂ ha₂))
  have hg_ch_inj : Set.InjOn g_ch ↑addrs := by
    rintro ⟨p₁, i₁⟩ ha₁ ⟨p₂, i₂⟩ ha₂ heq
    obtain ⟨_, hi₁⟩ := hmem_addrs.mp ha₁
    obtain ⟨_, hi₂⟩ := hmem_addrs.mp ha₂
    rw [hg_ch] at heq; dsimp only at heq
    have hm₁ : finsetEntry (childRow p₁) i₁ ∈
        N_child.filter (fun n => maxPrimeStem (maxPrimeStem n) = b * p₁) := by
      rw [← congrFun hchildRow p₁]; exact finsetEntry_mem hi₁
    have hm₂ : finsetEntry (childRow p₂) i₂ ∈
        N_child.filter (fun n => maxPrimeStem (maxPrimeStem n) = b * p₂) := by
      rw [← congrFun hchildRow p₂]; exact finsetEntry_mem hi₂
    have hp_eq : p₁ = p₂ := Nat.eq_of_mul_eq_mul_left hb_pos
      ((mem_filter.mp hm₁).2.symm.trans
        ((congrArg (fun n => maxPrimeStem (maxPrimeStem n)) heq).trans (mem_filter.mp hm₂).2))
    rcases hp_eq with rfl
    exact Prod.ext rfl (finsetEntry_inj hi₁ hi₂ heq)
  have haddrs_card : addrs.card = N_child.card := by
    rw [haddrs, ← hN_part, card_biUnion hdisj_childRow]
    refine (card_biUnion ?_).trans (sum_congr rfl fun p₁ _ => ?_)
    · intro p₁ _ p₁' _ hne
      refine disjoint_left.mpr fun pair hp₁ hp₂ => ?_
      obtain ⟨_, _, h1⟩ := mem_image.mp hp₁
      obtain ⟨_, _, h2⟩ := mem_image.mp hp₂
      exact hne ((Prod.ext_iff.mp (h1.trans h2.symm)).1)
    · rw [card_image_of_injOn (fun _ _ _ _ h => (Prod.ext_iff.mp h).2), card_range]
  obtain ⟨S_ch, hS_ch⟩ : ∃ S_ch : Finset ℕ, S_ch = addrs.image f_ch := ⟨_, rfl⟩
  have hS_ch_sub : S_ch ⊆ fibrePos X b := by
    rw [hS_ch]; intro m hm
    obtain ⟨⟨p₁, i⟩, ha, rfl⟩ := mem_image.mp hm
    exact (hch_spec ha).1
  have hS_ch_card : S_ch.card = N_child.card := by
    rw [hS_ch, card_image_of_injOn hf_ch_inj, haddrs_card]
  obtain ⟨P_rem, hP_rem⟩ : ∃ P_rem : Finset ℕ, P_rem = fibrePos X b \ S_ch := ⟨_, rfl⟩
  have hP_rem_card : P_rem.card = (fibrePos X b).card - N_child.card := by
    rw [hP_rem, card_sdiff_of_subset hS_ch_sub, hS_ch_card]
  have hroot_neg_le_Prem : (fibreNeg X b).card ≤ P_rem.card := by
    rw [hP_rem_card, hN_child_card, hC_sel]; omega
  obtain ⟨S_rt, hS_rt⟩ : ∃ S_rt : Finset ℕ,
      S_rt = (range (fibreNeg X b).card).image (finsetEntry P_rem) := ⟨_, rfl⟩
  have hS_rt_mem_Prem : ∀ m ∈ S_rt, m ∈ P_rem := by
    rw [hS_rt]; intro m hm
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hm
    exact finsetEntry_mem ((mem_range.mp hj).trans_le hroot_neg_le_Prem)
  have hdisj_S : Disjoint S_ch S_rt := by
    refine disjoint_right.mpr fun m hm_rt hm_ch => ?_
    have hm_rem := hS_rt_mem_Prem m hm_rt
    rw [hP_rem] at hm_rem
    exact (mem_sdiff.mp hm_rem).2 hm_ch
  have hS_rt_inj : Set.InjOn (finsetEntry P_rem) ↑(range (fibreNeg X b).card) :=
    fun _ hj₁ _ hj₂ heq => finsetEntry_inj
      ((mem_range.mp hj₁).trans_le hroot_neg_le_Prem)
      ((mem_range.mp hj₂).trans_le hroot_neg_le_Prem) heq
  have hS_rt_card : S_rt.card = (fibreNeg X b).card := by
    rw [hS_rt, card_image_of_injOn hS_rt_inj, card_range]
  obtain ⟨partner_b, hpartner⟩ : ∃ partner_b : ℕ → ℕ,
      partner_b = fun m =>
        if m ∈ S_ch then g_ch (unpair_ch m)
        else finsetEntry (fibreNeg X b) (finsetRank P_rem m) := ⟨_, rfl⟩
  have hpart_ch : ∀ a ∈ addrs, partner_b (f_ch a) = g_ch a := by
    intro a ha
    have hm : f_ch a ∈ S_ch := by rw [hS_ch]; exact mem_image_of_mem f_ch ha
    rw [hpartner]; dsimp only; rw [if_pos hm, hunpair_ch a ha]
  have hpart_rt : ∀ j ∈ range (fibreNeg X b).card,
      partner_b (finsetEntry P_rem j) = finsetEntry (fibreNeg X b) j := by
    intro j hj
    have hm_rt : finsetEntry P_rem j ∈ S_rt := by
      rw [hS_rt]; exact mem_image_of_mem (finsetEntry P_rem) hj
    have hnot_ch : finsetEntry P_rem j ∉ S_ch := disjoint_right.mp hdisj_S hm_rt
    rw [hpartner]; dsimp only
    rw [if_neg hnot_ch, finsetRank_entry ((mem_range.mp hj).trans_le hroot_neg_le_Prem)]
  let M_b : OppositeParityMatching GlobalDyadicOneTwoRel V_cl :=
    { sources := S_ch ∪ S_rt
      partner := partner_b
      sources_subset := fun m hm => by
        rw [hpos_cluster]
        rcases mem_union.mp hm with hm_ch | hm_rt
        · exact hS_ch_sub hm_ch
        · have hm_rem := hS_rt_mem_Prem m hm_rt
          rw [hP_rem] at hm_rem
          exact (mem_sdiff.mp hm_rem).1
      injOn := fun m₁ hm₁ m₂ hm₂ heq => by
        rcases mem_union.mp hm₁ with hc₁ | hr₁ <;> rcases mem_union.mp hm₂ with hc₂ | hr₂
        · rw [hS_ch] at hc₁ hc₂
          obtain ⟨a₁, ha₁, rfl⟩ := mem_image.mp hc₁
          obtain ⟨a₂, ha₂, rfl⟩ := mem_image.mp hc₂
          rw [hpart_ch a₁ ha₁, hpart_ch a₂ ha₂] at heq
          exact congrArg f_ch (hg_ch_inj ha₁ ha₂ heq)
        · rw [hS_ch] at hc₁; rw [hS_rt] at hr₂
          obtain ⟨⟨p₁, i⟩, ha₁, rfl⟩ := mem_image.mp hc₁
          obtain ⟨j₂, hj₂, rfl⟩ := mem_image.mp hr₂
          rw [hpart_ch (p₁, i) ha₁, hpart_rt j₂ hj₂] at heq
          exact False.elim (disjoint_right.mp hdisj_root_child_neg (hch_spec ha₁).2.2.1
            (heq ▸ finsetEntry_mem (mem_range.mp hj₂)))
        · rw [hS_rt] at hr₁; rw [hS_ch] at hc₂
          obtain ⟨j₁, hj₁, rfl⟩ := mem_image.mp hr₁
          obtain ⟨⟨p₂, i⟩, ha₂, rfl⟩ := mem_image.mp hc₂
          rw [hpart_rt j₁ hj₁, hpart_ch (p₂, i) ha₂] at heq
          exact False.elim (disjoint_left.mp hdisj_root_child_neg
            (finsetEntry_mem (mem_range.mp hj₁)) (heq ▸ (hch_spec ha₂).2.2.1))
        · rw [hS_rt] at hr₁ hr₂
          obtain ⟨j₁, hj₁, rfl⟩ := mem_image.mp hr₁
          obtain ⟨j₂, hj₂, rfl⟩ := mem_image.mp hr₂
          rw [hpart_rt j₁ hj₁, hpart_rt j₂ hj₂] at heq
          exact congrArg (finsetEntry P_rem)
            (finsetEntry_inj (mem_range.mp hj₁) (mem_range.mp hj₂) heq)
      partner_mem := fun m hm => by
        rw [hneg_cluster]
        rcases mem_union.mp hm with hc | hr
        · rw [hS_ch] at hc
          obtain ⟨⟨p₁, i⟩, ha, rfl⟩ := mem_image.mp hc
          rw [hpart_ch (p₁, i) ha]
          exact mem_union_right _ (hch_spec ha).2.2.1
        · rw [hS_rt] at hr
          obtain ⟨j, hj, rfl⟩ := mem_image.mp hr
          rw [hpart_rt j hj]
          exact mem_union_left _ (finsetEntry_mem (mem_range.mp hj))
      adj := fun m hm => by
        rcases mem_union.mp hm with hc | hr
        · rw [hS_ch] at hc
          obtain ⟨⟨p₁, i⟩, ha, rfl⟩ := mem_image.mp hc
          rw [hpart_ch (p₁, i) ha]
          exact (hch_spec ha).2.2.2
        · rw [hS_rt] at hr
          obtain ⟨j, hj, rfl⟩ := mem_image.mp hr
          rw [hpart_rt j hj]
          have hm_rem : finsetEntry P_rem j ∈ fibrePos X b \ S_ch := by
            rw [← hP_rem]; exact finsetEntry_mem ((mem_range.mp hj).trans_le hroot_neg_le_Prem)
          exact (evenPrefixCofactor_complete_bipartite_fibres hX1).2
            (mem_sdiff.mp hm_rem).1 (finsetEntry_mem (mem_range.mp hj)) }
  obtain ⟨τ_cl, hτ_cl⟩ : ∃ τ_cl : FactorizationInvolution GlobalDyadicOneTwoRel V_cl,
      τ_cl = FactorizationInvolution.ofMatching M_b := ⟨_, rfl⟩
  have hτ_cl_pos_card : τ_cl.movedPos.card = N_child.card + (fibreNeg X b).card := by
    rw [hτ_cl, FactorizationInvolution.ofMatching_movedPos]
    change (S_ch ∪ S_rt).card = _
    rw [card_union_of_disjoint hdisj_S, hS_ch_card, hS_rt_card]
  have hτ_cl_unm : τ_cl.unmatchedSet.card ≤ ⌊2 * s ^ 53⌋₊ := by
    have htot := τ_cl.card_unmatchedSet_add_movedSet
    rw [τ_cl.card_movedSet, hτ_cl_pos_card, hsq_cluster, hN_child_card, hC_sel] at htot
    omega
  have hτ_cl_unm_r : (τ_cl.unmatchedSet.card : ℝ) ≤ 4 * z ^ 53 := by
    refine (Nat.cast_le.mpr hτ_cl_unm).trans
      ((Nat.floor_le (mul_nonneg (by norm_num) (pow_nonneg hs0.le 53))).trans ?_)
    linarith only [hs53_hi]
  have hex_τ : ∃ τ_b : FactorizationInvolution GlobalDyadicOneTwoRel V_cl,
      (τ_b.unmatchedSet.card : ℝ) ≤ 4 * z ^ 53 := ⟨τ_cl, hτ_cl_unm_r⟩
  rw [hV_cl, hC_sel] at hex_τ
  exact ⟨hsel_props, hsel_le, hex_τ⟩

private lemma balanced_root_cluster_main (X : ℕ) (z S_surp H_lo S_cap : ℝ) (W₁ W₂ : Finset ℕ)
    (hX1 : 1 ≤ X) (hX64 : 64 ≤ (X : ℝ)) (hz4 : 4 ≤ z)
    (hz_surp : S_surp ≤ z) (hz_Hlo : H_lo ≤ z) (hz_Scap : S_cap ^ 6 ≤ z)
    (hz180 : z ^ (180 : ℕ) = (X : ℝ))
    (hLz_mert : 20 * (Real.log 2 + mertensBlockGapConst) ≤ Real.log z)
    (hlogX_eq : Real.log X = 180 * Real.log z)
    (hroot_eq : balancedRootCofactors X = (W₁ ×ˢ W₂).image fun pq => pq.1 * pq.2)
    (hW₁_sub : ∀ q ∈ W₁, q.Prime ∧ (3 / 4) * z ^ 28 < (q : ℝ) ∧ (q : ℝ) ≤ z ^ 28)
    (hW₂_sub : ∀ q ∈ W₂, q.Prime ∧ (3 / 4) * z ^ 32 < (q : ℝ) ∧ (q : ℝ) ≤ z ^ 32)
    (hsurp : ∀ {X b q₁ q₂ : ℕ}, 1 ≤ X → q₁.Prime → q₂.Prime → q₁ < q₂ → b = q₁ * q₂ →
      let T : ℝ := (X : ℝ) / b
      let s : ℝ := T ^ (1 / 120 : ℝ)
      S_surp ≤ s → (9 / 16) * s ^ 32 < (q₂ : ℝ) → (q₂ : ℝ) ≤ s ^ 32 →
      (fibreNeg X b).card ≤ (fibrePos X b).card ∧
      (1 / 1000) * T / Real.log T ≤ ((fibrePos X b).card : ℝ) - ((fibreNeg X b).card : ℝ) ∧
      ((fibrePos X b).card : ℝ) - ((fibreNeg X b).card : ℝ) ≤ (27 / 1000) * T / Real.log T)
    (hlo_2000 : ∀ R : ℝ, H_lo ≤ R → ∀ q : ℝ, 2 ≤ q → q ≤ 5 → ∀ u v : ℝ,
      R ≤ u → u ≤ v → v ≤ 2 * R → R / Real.log R ^ (0 : ℝ) ≤ v - u →
      (1 - 1 / 2000) * (v - u) / (q * Real.log R) ≤ ((windowPrimes (u / q) (v / q)).card : ℝ))
    (hS_cap : ∀ u : ℝ, S_cap ≤ u →
      10 * (cubeBandProducts u (u ^ 6) (2 * u ^ 6)).card ≤
        9 * (windowPrimes (u ^ 6) (2 * u ^ 6)).card) :
    ∀ b ∈ balancedRootCofactors X,
      b.primeFactors.card = 2 ∧
      (∀ a ∈ balancedChildSelection X b,
        a.primeFactors.card = 4 ∧ maxPrimeStem (maxPrimeStem a) = b ∧ fibrePos X a = ∅) ∧
      (1 / 1000) * z ^ 120 / Real.log X ≤
        (((fibrePos X b).card : ℝ) - ((fibreNeg X b).card : ℝ)) ∧
      (((∑ a ∈ insert b (balancedChildSelection X b),
        |((fibrePos X a).card : ℤ) - ((fibreNeg X a).card : ℤ)| : ℤ)) : ℝ) ≤
          (1 / 5) * z ^ 120 / Real.log X ∧
      ∃ τ_b : FactorizationInvolution GlobalDyadicOneTwoRel
          (fibreUnion X (insert b (balancedChildSelection X b))),
        (τ_b.unmatchedSet.card : ℝ) ≤ 4 * z ^ 53 := by
  have hLX : 0 < Real.log X := Real.log_pos (by linarith only [hX64])
  have hz0 : 0 < z := by linarith only [hz4]
  have hz1 : 1 ≤ z := by linarith only [hz4]
  intro b hb
  rw [hroot_eq] at hb
  obtain ⟨⟨q₁, q₂⟩, hpq, hb_symm⟩ := mem_image.mp hb
  have hb_eq : b = q₁ * q₂ := hb_symm.symm
  obtain ⟨hq₁W, hq₂W⟩ := mem_product.mp hpq
  dsimp only at hq₁W hq₂W
  obtain ⟨hq₁_pr, hq₁_lo, hq₁_hi⟩ := hW₁_sub q₁ hq₁W
  obtain ⟨hq₂_pr, hq₂_lo, hq₂_hi⟩ := hW₂_sub q₂ hq₂W
  have hq₁₂ : q₁ < q₂ := by
    have hlt28 : z ^ 28 < (3 / 4) * z ^ 32 := by
      have h4 : 4 * z ^ 28 ≤ z ^ 32 := by
        calc 4 * z ^ 28 ≤ z * z ^ 28 := mul_le_mul_of_nonneg_right hz4 (by positivity)
          _ = z ^ 29 := by ring
          _ ≤ z ^ 32 := pow_le_pow_right₀ hz1 (by decide)
      linarith [pow_pos hz0 28]
    exact_mod_cast (by linarith only [hq₁_hi, hq₂_lo, hlt28] : (q₁ : ℝ) < q₂)
  have hb_pos : 0 < b := hb_eq ▸ Nat.mul_pos hq₁_pr.pos hq₂_pr.pos
  have hb_r : (0 : ℝ) < b := by exact_mod_cast hb_pos
  have hb_card2 : b.primeFactors.card = 2 := by
    have ht : ∀ d ∈ q₁.primeFactors, d < q₂ := fun d hd =>
      (Nat.le_of_dvd hq₁_pr.pos (Nat.dvd_of_mem_primeFactors hd)).trans_lt hq₁₂
    rw [hb_eq, card_primeFactors_mul_larger_prime hq₁_pr.ne_zero hq₂_pr ht,
      hq₁_pr.primeFactors, card_singleton]
  have hb_lo : (9 / 16) * z ^ 60 < (b : ℝ) := by
    rw [hb_eq]; push_cast
    calc (9 / 16) * z ^ 60 = ((3 / 4) * z ^ 28) * ((3 / 4) * z ^ 32) := by ring
      _ < (q₁ : ℝ) * q₂ := mul_lt_mul'' hq₁_lo hq₂_lo (by positivity) (by positivity)
  have hb_hi : (b : ℝ) ≤ z ^ 60 := by
    rw [hb_eq]; push_cast
    calc (q₁ : ℝ) * q₂ ≤ z ^ 28 * z ^ 32 :=
          mul_le_mul hq₁_hi hq₂_hi (Nat.cast_nonneg _) (by positivity)
      _ = z ^ 60 := by ring
  obtain ⟨T, hT_def⟩ : ∃ T : ℝ, T = (X : ℝ) / b := ⟨_, rfl⟩
  have hT_pos : 0 < T := by rw [hT_def]; positivity
  have hT_lo : z ^ 120 ≤ T := by
    rw [hT_def, le_div_iff₀ hb_r]
    calc z ^ 120 * b ≤ z ^ 120 * z ^ 60 := mul_le_mul_of_nonneg_left hb_hi (by positivity)
      _ = X := by rw [← hz180]; ring
  have hT_hi : T < (16 / 9) * z ^ 120 := by
    rw [hT_def, div_lt_iff₀ hb_r]
    calc (X : ℝ) = (16 / 9) * z ^ 120 * ((9 / 16) * z ^ 60) := by rw [← hz180]; ring
      _ < (16 / 9) * z ^ 120 * b := mul_lt_mul_of_pos_left hb_lo (by positivity)
  obtain ⟨s, hs_def⟩ : ∃ s : ℝ, s = T ^ (1 / 120 : ℝ) := ⟨_, rfl⟩
  have hs0_nn : 0 ≤ s := by rw [hs_def]; exact Real.rpow_nonneg hT_pos.le _
  have hs120 : s ^ (120 : ℕ) = T := by
    rw [hs_def, ← Real.rpow_natCast, ← Real.rpow_mul hT_pos.le]; norm_num
  have hzs : z ≤ s :=
    (pow_le_pow_iff_left₀ hz0.le hs0_nn (by decide : 120 ≠ 0)).mp (hT_lo.trans_eq hs120.symm)
  have hs4 : 4 ≤ s := hz4.trans hzs
  have hs1 : 1 ≤ s := by linarith only [hs4]
  have hs0 : 0 < s := by linarith only [hs4]
  have hs53_hi : s ^ 53 ≤ 2 * z ^ 53 := by
    apply (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by decide : 120 ≠ 0)).mp
    have h1 : (s ^ 53) ^ 120 = T ^ 53 := by rw [← hs120]; ring
    have h2 : (2 * z ^ 53) ^ 120 = (2 : ℝ) ^ 120 * (z ^ 120) ^ 53 := by ring
    rw [h1, h2]
    have hT_le_2 : T ≤ 2 * z ^ 120 := hT_hi.le.trans
      (mul_le_mul_of_nonneg_right (by norm_num : (16 / 9 : ℝ) ≤ 2) (by positivity))
    calc T ^ 53 ≤ (2 * z ^ 120) ^ 53 := pow_le_pow_left₀ hT_pos.le hT_le_2 53
      _ = (2 : ℝ) ^ 53 * (z ^ 120) ^ 53 := by ring
      _ ≤ (2 : ℝ) ^ 120 * (z ^ 120) ^ 53 :=
          mul_le_mul_of_nonneg_right
            (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by decide : 53 ≤ 120))
            (by positivity)
  have hs32_lt_43 : s ^ 32 < (4 / 3) * z ^ 32 := by
    apply (pow_lt_pow_iff_left₀ (by positivity) (by positivity) (by decide : 15 ≠ 0)).mp
    have h1 : (s ^ 32) ^ 15 = T ^ 4 := by rw [← hs120]; ring
    have h2 : ((4 / 3) * z ^ 32) ^ 15 = (4 / 3 : ℝ) ^ 15 * (z ^ 120) ^ 4 := by ring
    rw [h1, h2]
    have h3 : T ^ 4 < ((16 / 9) * z ^ 120) ^ 4 :=
      pow_lt_pow_left₀ hT_hi hT_pos.le (by decide : 4 ≠ 0)
    have h4 : ((16 / 9) * z ^ 120) ^ 4 = (16 / 9 : ℝ) ^ 4 * (z ^ 120) ^ 4 := by ring
    rw [h4] at h3
    exact h3.trans_le (mul_le_mul_of_nonneg_right (by norm_num) (by positivity))
  have hq₂_s_lo : (9 / 16) * s ^ 32 < (q₂ : ℝ) := by linarith only [hs32_lt_43, hq₂_lo]
  have hq₂_s_hi : (q₂ : ℝ) ≤ s ^ 32 := hq₂_hi.trans (pow_le_pow_left₀ hz0.le hzs 32)
  have hsurp_call := hsurp hX1 hq₁_pr hq₂_pr hq₁₂ hb_eq
  dsimp only at hsurp_call
  rw [← hT_def, ← hs_def] at hsurp_call
  obtain ⟨hneg_le_pos, hsurp_lo, hsurp_hi⟩ :=
    hsurp_call (hz_surp.trans hzs) hq₂_s_lo hq₂_s_hi
  have hT_le_X : T ≤ X := by rw [hT_def]; exact div_le_self (Nat.cast_nonneg X) (by exact_mod_cast hb_pos)
  have hlogT_le_X : Real.log T ≤ Real.log X := Real.log_le_log hT_pos hT_le_X
  have hlogT_ge_X : (2 / 3) * Real.log X ≤ Real.log T := by
    have h := Real.log_le_log (pow_pos hz0 120) hT_lo
    rw [Real.log_pow] at h; push_cast at h
    rw [hlogX_eq]; linarith only [h]
  have hsurp_X_lo : (1 / 1000) * z ^ 120 / Real.log X ≤
      ((fibrePos X b).card : ℝ) - ((fibreNeg X b).card : ℝ) := by
    refine le_trans ?_ hsurp_lo
    calc (1 / 1000) * z ^ 120 / Real.log X
        ≤ (1 / 1000) * T / Real.log X :=
          div_le_div_of_nonneg_right (by linarith only [hT_lo]) hLX.le
      _ ≤ (1 / 1000) * T / Real.log T :=
          div_le_div_of_nonneg_left (by positivity)
            (Real.log_pos (by nlinarith [pow_pos hs0 120, one_le_pow₀ hs1 (n := 120), hs4, hs120]))
            hlogT_le_X
  obtain ⟨P₁_b, hP₁_def⟩ : ∃ P₁_b : Finset ℕ, P₁_b = windowPrimes (s ^ 32) (s ^ 35) := ⟨_, rfl⟩
  obtain ⟨P₂_b, hP₂_def⟩ : ∃ P₂_b : Finset ℕ, P₂_b = windowPrimes (s ^ 35) (s ^ 42) := ⟨_, rfl⟩
  have hpool_eq : balancedChildPool X b =
      (P₁_b ×ˢ P₂_b).image fun p₁₂ => b * p₁₂.1 * p₁₂.2 := by
    dsimp only [balancedChildPool]
    rw [← hT_def, ← hs_def, ← hP₁_def, ← hP₂_def]
    ext a
    simp only [mem_biUnion, mem_image, mem_product, Prod.exists]
    exact ⟨fun ⟨p₁, hp₁, p₂, hp₂, h⟩ => ⟨p₁, p₂, ⟨hp₁, hp₂⟩, h⟩,
      fun ⟨p₁, p₂, ⟨hp₁, hp₂⟩, h⟩ => ⟨p₁, hp₁, p₂, hp₂, h⟩⟩
  obtain ⟨hchild_elem, hpool_supply⟩ :=
    balanced_child_pool_bounds X b q₁ q₂ z T s H_lo P₁_b P₂_b hX1 hq₁_pr hq₂_pr hq₁₂ hb_eq hz4
      hT_def hs4 hs120 hzs hz_Hlo hLz_mert hq₂_s_hi hneg_le_pos hsurp_hi
      hP₁_def hP₂_def hpool_eq hlo_2000
  obtain ⟨hsel_props, hsel_le, τ_b, hτ_b_unm_r⟩ :=
    balanced_cluster_involution_exists X b q₁ q₂ z T s S_cap P₁_b P₂_b hX1 hq₁_pr hq₂_pr hq₁₂
      hb_eq hT_def hs4 hs120 hzs hz_Scap hs53_hi hq₂_s_hi hneg_le_pos
      hP₁_def hP₂_def hpool_eq hchild_elem hpool_supply hS_cap
  have hb_not_sel : b ∉ balancedChildSelection X b := fun hb_in => by
    have := (hsel_props b hb_in).1; omega
  have hord_cluster_hi :
      (((∑ a ∈ insert b (balancedChildSelection X b),
        |((fibrePos X a).card : ℤ) - ((fibreNeg X a).card : ℤ)| : ℤ)) : ℝ) ≤
        (1 / 5) * z ^ 120 / Real.log X := by
    rw [sum_insert hb_not_sel]
    have hroot_abs : |((fibrePos X b).card : ℤ) - ((fibreNeg X b).card : ℤ)| =
        (((fibrePos X b).card - (fibreNeg X b).card : ℕ) : ℤ) := by
      rw [Nat.cast_sub hneg_le_pos, abs_of_nonneg (by omega)]
    have hchild_abs : ∑ a ∈ balancedChildSelection X b,
        |((fibrePos X a).card : ℤ) - ((fibreNeg X a).card : ℤ)| =
        ∑ a ∈ balancedChildSelection X b, ((fibreNeg X a).card : ℤ) := by
      refine sum_congr rfl fun a ha => ?_
      rw [(hsel_props a ha).2.2, card_empty, Nat.cast_zero, zero_sub, abs_neg,
        abs_of_nonneg (Nat.cast_nonneg _)]
    rw [hroot_abs, hchild_abs]
    push_cast
    have h2surp : (((fibrePos X b).card - (fibreNeg X b).card : ℕ) : ℝ) +
        (∑ a ∈ balancedChildSelection X b, ((fibreNeg X a).card : ℝ)) ≤
        2 * (((fibrePos X b).card : ℝ) - ((fibreNeg X b).card : ℝ)) := by
      have h1 : (∑ a ∈ balancedChildSelection X b, ((fibreNeg X a).card : ℝ)) ≤
          (((fibrePos X b).card - (fibreNeg X b).card : ℕ) : ℝ) := by exact_mod_cast hsel_le
      rw [Nat.cast_sub hneg_le_pos] at h1 ⊢
      linarith only [h1]
    refine h2surp.trans ?_
    calc 2 * (((fibrePos X b).card : ℝ) - ((fibreNeg X b).card : ℝ))
        ≤ 2 * ((27 / 1000) * T / Real.log T) :=
          mul_le_mul_of_nonneg_left hsurp_hi (by norm_num)
      _ ≤ 2 * ((27 / 1000) * ((16 / 9) * z ^ 120) / ((2 / 3) * Real.log X)) :=
          mul_le_mul_of_nonneg_left
            ((div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hT_hi.le (by norm_num))
              (by linarith only [hlogT_ge_X, hLX])).trans
              (div_le_div_of_nonneg_left
                (mul_nonneg (by norm_num) (mul_nonneg (by norm_num) (pow_nonneg hz0.le 120)))
                (mul_pos (by norm_num) hLX) hlogT_ge_X))
            (by norm_num)
      _ ≤ (1 / 5) * z ^ 120 / Real.log X := by
          rw [show 2 * ((27 / 1000 : ℝ) * ((16 / 9) * z ^ 120) / ((2 / 3) * Real.log X)) =
            (18 / 125) * (z ^ 120 / Real.log X) by ring, mul_div_assoc]
          exact mul_le_mul_of_nonneg_right (by norm_num) (div_nonneg (pow_nonneg hz0.le 120) hLX.le)
  exact ⟨hb_card2, hsel_props, hsurp_X_lo, hord_cluster_hi, τ_b, hτ_b_unm_r⟩

private theorem disjoint_fibreUnion_of_disjoint {X : ℕ} (hX1 : 1 ≤ X) {A₁ A₂ : Finset ℕ}
    (hdisj : Disjoint A₁ A₂) : Disjoint (fibreUnion X A₁) (fibreUnion X A₂) := by
  refine disjoint_left.mpr fun n hn₁ hn₂ => ?_
  unfold fibreUnion at hn₁ hn₂
  obtain ⟨a₁, ha₁, hna₁⟩ := mem_biUnion.mp hn₁
  obtain ⟨a₂, ha₂, hna₂⟩ := mem_biUnion.mp hn₂
  have ha_ne : a₁ ≠ a₂ := fun heq => disjoint_left.mp hdisj ha₁ (heq ▸ ha₂)
  have hdis := (evenPrefixCofactor_complete_bipartite_fibres hX1).1 ha_ne
  rcases mem_union.mp hna₁ with hp₁ | hn₁' <;> rcases mem_union.mp hna₂ with hp₂ | hn₂'
  · exact disjoint_left.mp hdis.1 hp₁ hp₂
  · exact disjoint_left.mp (disjoint_posParity_negParity _)
      ((mem_filter.mp hp₁).1) ((mem_filter.mp hn₂').1)
  · exact disjoint_right.mp (disjoint_posParity_negParity _)
      ((mem_filter.mp hn₁').1) ((mem_filter.mp hp₂).1)
  · exact disjoint_left.mp hdis.2 hn₁' hn₂'

/-- **Main Power-Saving Theorem on a Self-Contained Growing Class of Cofactor Fibres**:
there exist explicit constants `0 < c_fib`, `0 < c₁ < c₂`, and `X₀ : ℕ` such that for every
`X ≥ X₀`:
1. **Growing deficient fibre class**: `#(balancedFibreClass X) ≥ c_fib * X^{1/3} / (log X)²`;
2. **Exact `Θ(X / (log X)³)` ordered-cofactor debt**: every `OrderedFibreRel` involution `τ₀` on
   `fibreUnion X (balancedFibreClass X)` leaves at least `c₁ * X / (log X)³` unmatched vertices,
   and the optimal ordered-cofactor debt satisfies `≤ c₂ * X / (log X)³`;
3. **Explicit closed `GlobalDyadicOneTwoRel` involution with `O(X^{113/180})` unmatched remainder**:
   there exists an explicit `FactorizationInvolution GlobalDyadicOneTwoRel
   (fibreUnion X (balancedFibreClass X))` `τ` (closed inside `balancedFibreClass X`, with zero
   double-used endpoints) satisfying
   `τ.unmatchedSet.card ≤ 4 * X^{113/180} ≤ 4 * X^{2/3}` and
   `|∑_{n ∈ fibreUnion X (balancedFibreClass X)} μ n| ≤ 4 * X^{113/180}`. -/
theorem eventually_balancedFibreClass_power_saving :
    ∃ (c_fib c₁ c₂ : ℝ), 0 < c_fib ∧ 0 < c₁ ∧ c₁ < c₂ ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      c_fib * (X : ℝ) ^ (1 / 3 : ℝ) / Real.log X ^ (2 : ℕ) ≤
        ((balancedFibreClass X).card : ℝ) ∧
      (∀ τ₀ : FactorizationInvolution OrderedFibreRel (fibreUnion X (balancedFibreClass X)),
        c₁ * (X : ℝ) / Real.log X ^ (3 : ℕ) ≤ (τ₀.unmatchedSet.card : ℝ)) ∧
      (∃ τ_ord : FactorizationInvolution OrderedFibreRel (fibreUnion X (balancedFibreClass X)),
        (τ_ord.unmatchedSet.card : ℝ) ≤ c₂ * (X : ℝ) / Real.log X ^ (3 : ℕ)) ∧
      (∃ τ : FactorizationInvolution GlobalDyadicOneTwoRel (fibreUnion X (balancedFibreClass X)),
        (τ.unmatchedSet.card : ℝ) ≤ 4 * (X : ℝ) ^ (113 / 180 : ℝ) ∧
        (τ.unmatchedSet.card : ℝ) ≤ 4 * (X : ℝ) ^ (2 / 3 : ℝ) ∧
        |(∑ n ∈ fibreUnion X (balancedFibreClass X), μ n : ℝ)| ≤
          4 * (X : ℝ) ^ (113 / 180 : ℝ)) := by
  obtain ⟨U_43, _, hw_43⟩ := exists_const_ratio_windowPrimes_bounds (α := 4 / 3) (by norm_num)
  obtain ⟨S_surp, _, hsurp⟩ := eventually_root_positive_surplus_bounds
  obtain ⟨H_lo, _, hlo_2000⟩ :=
    exists_card_windowPrimes_div_ge (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2000)
  obtain ⟨S_cap, hS_cap⟩ := eventually_atTop.mp eventually_cubeBandProducts_nine_tenths
  set c_fib : ℝ := (1 / 8) * (1 / 8) * (9 / 16)
  set c₁ : ℝ := c_fib * (1 / 1000)
  set c₂ : ℝ := 20
  let C_mert : ℝ := Real.log 2 + mertensBlockGapConst
  have hrpow180 : Tendsto (fun x : ℝ => x ^ (1 / 180 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have hev : ∀ᶠ x : ℝ in atTop,
      64 ≤ x ∧ max 4 (max S_surp H_lo) ≤ x ^ (1 / 180 : ℝ) ∧
      (4 / 3) * U_43 ≤ (x ^ (1 / 180 : ℝ)) ^ 28 ∧
      S_cap ^ 6 ≤ x ^ (1 / 180 : ℝ) ∧
      max (20 * C_mert) (12 * Real.log 4) ≤ Real.log (x ^ (1 / 180 : ℝ)) := by
    have hz28 : Tendsto (fun x : ℝ => (x ^ (1 / 180 : ℝ)) ^ 28) atTop atTop :=
      (tendsto_pow_atTop (by decide : 28 ≠ 0)).comp hrpow180
    exact (eventually_ge_atTop 64).and ((hrpow180.eventually_ge_atTop _).and
      ((hz28.eventually_ge_atTop _).and ((hrpow180.eventually_ge_atTop _).and
        ((Real.tendsto_log_atTop.comp hrpow180).eventually_ge_atTop _))))
  obtain ⟨X_cut, hX_cut⟩ := eventually_atTop.mp hev
  refine ⟨c_fib, c₁, c₂, by positivity, by positivity, by norm_num [c₁, c_fib, c₂],
    max 2 ⌈X_cut⌉₊, fun X hX => ?_⟩
  have hX1 : 1 ≤ X := le_trans (by decide : 1 ≤ 2) ((le_max_left _ _).trans hX)
  have hX_ge : X_cut ≤ (X : ℝ) :=
    (Nat.le_ceil X_cut).trans (by exact_mod_cast (le_max_right _ _).trans hX)
  obtain ⟨hX64, hz_max, hz28_U, hz_Scap, hLz_max⟩ := hX_cut X hX_ge
  have hX0 : (0 : ℝ) < X := by linarith only [hX64]
  have hLX : 0 < Real.log X := Real.log_pos (by linarith only [hX64])
  obtain ⟨z, hz_def⟩ : ∃ z : ℝ, z = (X : ℝ) ^ (1 / 180 : ℝ) := ⟨_, rfl⟩
  rw [← hz_def] at hz_max hz28_U hz_Scap hLz_max
  have hz4 : 4 ≤ z := (le_max_left _ _).trans hz_max
  have hz_surp : S_surp ≤ z := (le_max_left _ _).trans ((le_max_right _ _).trans hz_max)
  have hz_Hlo : H_lo ≤ z := (le_max_right _ _).trans ((le_max_right _ _).trans hz_max)
  have hz0 : 0 < z := by linarith only [hz4]
  have hz1 : 1 ≤ z := by linarith only [hz4]
  have hz180 : z ^ (180 : ℕ) = (X : ℝ) := by
    rw [hz_def, ← Real.rpow_natCast, ← Real.rpow_mul hX0.le]; norm_num
  have hz60 : z ^ (60 : ℕ) = (X : ℝ) ^ (1 / 3 : ℝ) := by
    rw [hz_def, ← Real.rpow_natCast, ← Real.rpow_mul hX0.le]; norm_num
  have hz113 : z ^ (113 : ℕ) = (X : ℝ) ^ (113 / 180 : ℝ) := by
    rw [hz_def, ← Real.rpow_natCast, ← Real.rpow_mul hX0.le]; norm_num
  have hLz_mert : 20 * C_mert ≤ Real.log z := (le_max_left _ _).trans hLz_max
  have hLz_4 : 12 * Real.log 4 ≤ Real.log z := (le_max_right _ _).trans hLz_max
  have hlogX_eq : Real.log X = 180 * Real.log z := by
    have : Real.log (z ^ (180 : ℕ)) = Real.log X := by rw [hz180]
    rw [Real.log_pow] at this; push_cast at this; linarith
  obtain ⟨W₁, hW₁_def⟩ : ∃ W₁ : Finset ℕ, W₁ = windowPrimes ((3 / 4) * z ^ 28) (z ^ 28) := ⟨_, rfl⟩
  obtain ⟨W₂, hW₂_def⟩ : ∃ W₂ : Finset ℕ, W₂ = windowPrimes ((3 / 4) * z ^ 32) (z ^ 32) := ⟨_, rfl⟩
  have hroot_eq : balancedRootCofactors X = (W₁ ×ˢ W₂).image fun pq => pq.1 * pq.2 := by
    dsimp only [balancedRootCofactors]; rw [← hz_def, ← hW₁_def, ← hW₂_def]
  have hW₁_sub : ∀ q ∈ W₁, q.Prime ∧ (3 / 4) * z ^ 28 < (q : ℝ) ∧ (q : ℝ) ≤ z ^ 28 := fun q hq => by
    rw [hW₁_def] at hq; exact (mem_windowPrimes (by positivity) (by positivity)).mp hq
  have hW₂_sub : ∀ q ∈ W₂, q.Prime ∧ (3 / 4) * z ^ 32 < (q : ℝ) ∧ (q : ℝ) ≤ z ^ 32 := fun q hq => by
    rw [hW₂_def] at hq; exact (mem_windowPrimes (by positivity) (by positivity)).mp hq
  have hinj_root : Set.InjOn (fun pq : ℕ × ℕ => pq.1 * pq.2) ↑(W₁ ×ˢ W₂) := by
    rintro ⟨q₁, q₂⟩ hpq₁ ⟨q₁', q₂'⟩ hpq₂ heq
    dsimp only at heq
    obtain ⟨hq₁, hq₂⟩ := mem_product.mp hpq₁
    obtain ⟨hq₁', hq₂'⟩ := mem_product.mp hpq₂
    dsimp only at hq₁ hq₂ hq₁' hq₂'
    obtain ⟨hq₁_pr, _, hq₁_hi⟩ := hW₁_sub q₁ hq₁
    obtain ⟨hq₂_pr, _, _⟩ := hW₂_sub q₂ hq₂
    obtain ⟨hq₁'_pr, _, _⟩ := hW₁_sub q₁' hq₁'
    obtain ⟨hq₂'_pr, hq₂'_lo, _⟩ := hW₂_sub q₂' hq₂'
    have hlt : q₁ < q₂' := by
      have : z ^ 28 < (3 / 4) * z ^ 32 := by
        have h4 : 4 * z ^ 28 ≤ z ^ 32 := by
          calc 4 * z ^ 28 ≤ z * z ^ 28 := mul_le_mul_of_nonneg_right hz4 (by positivity)
            _ = z ^ 29 := by ring
            _ ≤ z ^ 32 := pow_le_pow_right₀ hz1 (by decide)
        linarith [pow_pos hz0 28]
      exact_mod_cast (by linarith : (q₁ : ℝ) < q₂')
    have heq1 : q₁ = q₁' := by
      rcases hq₁_pr.dvd_mul.mp (heq ▸ dvd_mul_right q₁ q₂) with h1 | h2
      · exact (Nat.prime_dvd_prime_iff_eq hq₁_pr hq₁'_pr).mp h1
      · exact False.elim (hlt.ne ((Nat.prime_dvd_prime_iff_eq hq₁_pr hq₂'_pr).mp h2))
    subst heq1
    exact Prod.ext rfl (Nat.eq_of_mul_eq_mul_left hq₁_pr.pos heq)
  have hW₁_bounds :
      (1 / 8) * ((3 / 4) * z ^ 28) / Real.log X ≤ (W₁.card : ℝ) ∧
      (W₁.card : ℝ) ≤ 10 * z ^ 28 / Real.log X ∧
      (W₁.card : ℝ) ≤ z ^ 28 := by
    have h43 : (4 / 3 : ℝ) * ((3 / 4) * z ^ 28) = z ^ 28 := by ring
    have hw := hw_43 ((3 / 4) * z ^ 28) (by linarith)
    rw [h43, ← hW₁_def] at hw
    have hz28_le_X : z ^ 28 ≤ X := by rw [← hz180]; exact pow_le_pow_right₀ hz1 (by decide)
    have hl_hi : Real.log (z ^ 28) ≤ Real.log X := Real.log_le_log (by positivity) hz28_le_X
    have hl_lo : (1 / 10) * Real.log X ≤ Real.log ((3 / 4) * z ^ 28) := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, hlogX_eq]
      have h34 : -Real.log 4 ≤ Real.log (3 / 4 : ℝ) := by
        have hl := Real.log_le_log (by norm_num) (show (1 / 4 : ℝ) ≤ 3 / 4 by norm_num)
        rwa [one_div, Real.log_inv] at hl
      norm_num1; linarith [hLz_4]
    have htriv : W₁.card ≤ ⌊z ^ 28⌋₊ := by
      have hsub : W₁ ⊆ Icc 1 ⌊z ^ 28⌋₊ := fun p hp => by
        obtain ⟨hpp, _, hp_hi⟩ := hW₁_sub p hp
        exact mem_Icc.mpr ⟨hpp.pos, Nat.le_floor hp_hi⟩
      simpa using card_le_card hsub
    refine ⟨?_, ?_, (Nat.cast_le.mpr htriv).trans (Nat.floor_le (by positivity))⟩
    · calc (1 / 8) * ((3 / 4) * z ^ 28) / Real.log X
          ≤ ((4 / 3 - 1) / 2) * ((3 / 4) * z ^ 28) / Real.log (z ^ 28) := by
            have hnum : (1 / 8 : ℝ) * ((3 / 4) * z ^ 28) ≤
                ((4 / 3 - 1) / 2) * ((3 / 4) * z ^ 28) := by linarith [pow_pos hz0 28]
            exact (div_le_div_of_nonneg_right hnum hLX.le).trans
              (div_le_div_of_nonneg_left (by positivity)
                (Real.log_pos (by nlinarith [pow_pos hz0 28, one_le_pow₀ hz1 (n := 28)])) hl_hi)
        _ ≤ (W₁.card : ℝ) := hw.1
    · calc (W₁.card : ℝ)
          ≤ (2 * (4 / 3 - 1)) * ((3 / 4) * z ^ 28) / Real.log ((3 / 4) * z ^ 28) := hw.2
        _ ≤ (1 / 2) * z ^ 28 / ((1 / 10) * Real.log X) := by
            have : (2 * (4 / 3 - 1) : ℝ) * ((3 / 4) * z ^ 28) = (1 / 2) * z ^ 28 := by ring
            rw [this]
            exact div_le_div_of_nonneg_left (by positivity) (by positivity) hl_lo
        _ ≤ 10 * z ^ 28 / Real.log X := by
            rw [show (1 / 2 : ℝ) * z ^ 28 / ((1 / 10) * Real.log X) = 5 * z ^ 28 / Real.log X by ring]
            exact div_le_div_of_nonneg_right (by linarith [pow_pos hz0 28]) hLX.le
  have hW₂_bounds :
      (1 / 8) * ((3 / 4) * z ^ 32) / Real.log X ≤ (W₂.card : ℝ) ∧
      (W₂.card : ℝ) ≤ 10 * z ^ 32 / Real.log X ∧
      (W₂.card : ℝ) ≤ z ^ 32 := by
    have h43 : (4 / 3 : ℝ) * ((3 / 4) * z ^ 32) = z ^ 32 := by ring
    have hz28_32 : z ^ 28 ≤ z ^ 32 := pow_le_pow_right₀ hz1 (by decide)
    have hw := hw_43 ((3 / 4) * z ^ 32) (by linarith)
    rw [h43, ← hW₂_def] at hw
    have hz32_le_X : z ^ 32 ≤ X := by rw [← hz180]; exact pow_le_pow_right₀ hz1 (by decide)
    have hl_hi : Real.log (z ^ 32) ≤ Real.log X := Real.log_le_log (by positivity) hz32_le_X
    have hl_lo : (1 / 10) * Real.log X ≤ Real.log ((3 / 4) * z ^ 32) := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, hlogX_eq]
      have h34 : -Real.log 4 ≤ Real.log (3 / 4 : ℝ) := by
        have hl := Real.log_le_log (by norm_num) (show (1 / 4 : ℝ) ≤ 3 / 4 by norm_num)
        rwa [one_div, Real.log_inv] at hl
      norm_num1; linarith [hLz_4]
    have htriv : W₂.card ≤ ⌊z ^ 32⌋₊ := by
      have hsub : W₂ ⊆ Icc 1 ⌊z ^ 32⌋₊ := fun p hp => by
        obtain ⟨hpp, _, hp_hi⟩ := hW₂_sub p hp
        exact mem_Icc.mpr ⟨hpp.pos, Nat.le_floor hp_hi⟩
      simpa using card_le_card hsub
    refine ⟨?_, ?_, (Nat.cast_le.mpr htriv).trans (Nat.floor_le (by positivity))⟩
    · calc (1 / 8) * ((3 / 4) * z ^ 32) / Real.log X
          ≤ ((4 / 3 - 1) / 2) * ((3 / 4) * z ^ 32) / Real.log (z ^ 32) := by
            have hnum : (1 / 8 : ℝ) * ((3 / 4) * z ^ 32) ≤
                ((4 / 3 - 1) / 2) * ((3 / 4) * z ^ 32) := by linarith [pow_pos hz0 32]
            exact (div_le_div_of_nonneg_right hnum hLX.le).trans
              (div_le_div_of_nonneg_left (by positivity)
                (Real.log_pos (by nlinarith [pow_pos hz0 32, one_le_pow₀ hz1 (n := 32)])) hl_hi)
        _ ≤ (W₂.card : ℝ) := hw.1
    · calc (W₂.card : ℝ)
          ≤ (2 * (4 / 3 - 1)) * ((3 / 4) * z ^ 32) / Real.log ((3 / 4) * z ^ 32) := hw.2
        _ ≤ (1 / 2) * z ^ 32 / ((1 / 10) * Real.log X) := by
            have : (2 * (4 / 3 - 1) : ℝ) * ((3 / 4) * z ^ 32) = (1 / 2) * z ^ 32 := by ring
            rw [this]
            exact div_le_div_of_nonneg_left (by positivity) (by positivity) hl_lo
        _ ≤ 10 * z ^ 32 / Real.log X := by
            rw [show (1 / 2 : ℝ) * z ^ 32 / ((1 / 10) * Real.log X) = 5 * z ^ 32 / Real.log X by ring]
            exact div_le_div_of_nonneg_right (by linarith [pow_pos hz0 32]) hLX.le
  have hroot_card_eq : (balancedRootCofactors X).card = W₁.card * W₂.card := by
    rw [hroot_eq, card_image_of_injOn hinj_root, card_product]
  have hroot_card_lo : c_fib * (X : ℝ) ^ (1 / 3 : ℝ) / Real.log X ^ (2 : ℕ) ≤
      ((balancedRootCofactors X).card : ℝ) := by
    rw [hroot_card_eq, Nat.cast_mul, ← hz60]
    calc c_fib * z ^ 60 / Real.log X ^ (2 : ℕ)
        = ((1 / 8) * ((3 / 4) * z ^ 28) / Real.log X) *
            ((1 / 8) * ((3 / 4) * z ^ 32) / Real.log X) := by dsimp [c_fib]; ring
      _ ≤ (W₁.card : ℝ) * (W₂.card : ℝ) :=
          mul_le_mul hW₁_bounds.1 hW₂_bounds.1 (by positivity) (Nat.cast_nonneg _)
  have hroot_card_hi : ((balancedRootCofactors X).card : ℝ) ≤
      100 * z ^ 60 / Real.log X ^ (2 : ℕ) := by
    rw [hroot_card_eq, Nat.cast_mul]
    calc (W₁.card : ℝ) * (W₂.card : ℝ)
        ≤ (10 * z ^ 28 / Real.log X) * (10 * z ^ 32 / Real.log X) :=
          mul_le_mul hW₁_bounds.2.1 hW₂_bounds.2.1 (Nat.cast_nonneg _) (by positivity)
      _ = 100 * z ^ 60 / Real.log X ^ (2 : ℕ) := by ring
  have hroot_card_triv : ((balancedRootCofactors X).card : ℝ) ≤ z ^ 60 := by
    rw [hroot_card_eq, Nat.cast_mul]
    calc (W₁.card : ℝ) * (W₂.card : ℝ) ≤ z ^ 28 * z ^ 32 :=
          mul_le_mul hW₁_bounds.2.2 hW₂_bounds.2.2 (Nat.cast_nonneg _) (by positivity)
      _ = z ^ 60 := by ring
  let clusterCofactors : ℕ → Finset ℕ := fun b => insert b (balancedChildSelection X b)
  let clusterVerts : ℕ → Finset ℕ := fun b => fibreUnion X (clusterCofactors b)
  have hcluster_main := balanced_root_cluster_main X z S_surp H_lo S_cap W₁ W₂ hX1 hX64 hz4
    hz_surp hz_Hlo hz_Scap hz180 hLz_mert hlogX_eq hroot_eq hW₁_sub hW₂_sub hsurp hlo_2000 hS_cap
  -- Global disjointness of `clusterCofactors b` and `clusterVerts b` across `balancedRootCofactors X`
  let B_roots := balancedRootCofactors X
  have hdisj_cof : (B_roots : Set ℕ).PairwiseDisjoint clusterCofactors := by
    intro b₁ hb₁ b₂ hb₂ hne
    refine disjoint_left.mpr fun a ha₁ ha₂ => ?_
    rcases mem_insert.mp ha₁ with rfl | hc₁ <;> rcases mem_insert.mp ha₂ with rfl | hc₂
    · exact hne rfl
    · have h2 := (hcluster_main a hb₁).1
      have h4 := ((hcluster_main b₂ hb₂).2.1 a hc₂).1
      omega
    · have h4 := ((hcluster_main b₁ hb₁).2.1 a hc₁).1
      have h2 := (hcluster_main a hb₂).1
      omega
    · have hs₁ := ((hcluster_main b₁ hb₁).2.1 a hc₁).2.1
      have hs₂ := ((hcluster_main b₂ hb₂).2.1 a hc₂).2.1
      exact hne (hs₁.symm.trans hs₂)
  have hdisj_verts : (B_roots : Set ℕ).PairwiseDisjoint clusterVerts :=
    fun _ hb₁ _ hb₂ hne => disjoint_fibreUnion_of_disjoint hX1 (hdisj_cof hb₁ hb₂ hne)
  have hcover_cof : B_roots.biUnion clusterCofactors = balancedFibreClass X := rfl
  have hcover_verts : B_roots.biUnion clusterVerts = fibreUnion X (balancedFibreClass X) := by
    dsimp [clusterVerts, fibreUnion]
    rw [← hcover_cof, biUnion_biUnion]
  -- 1. `#(balancedFibreClass X) ≥ c_fib * X^{1/3} / (log X)²`
  have hsub_roots : B_roots ⊆ balancedFibreClass X := fun b hb =>
    mem_biUnion.mpr ⟨b, hb, mem_insert_self b _⟩
  have hcard_class_ge : c_fib * (X : ℝ) ^ (1 / 3 : ℝ) / Real.log X ^ (2 : ℕ) ≤
      ((balancedFibreClass X).card : ℝ) :=
    hroot_card_lo.trans (by exact_mod_cast card_le_card hsub_roots)
  -- 2. Exact `Θ(X / (log X)³)` ordered-cofactor bounds via `fibreUnion_ordered_and_global_bounds`
  obtain ⟨hord_lo_all, ⟨τ_ord, hτ_ord_eq⟩, _⟩ :=
    fibreUnion_ordered_and_global_bounds hX1 (balancedFibreClass X)
  have hord_sum_lo : c₁ * (X : ℝ) / Real.log X ^ (3 : ℕ) ≤
      (((∑ a ∈ balancedFibreClass X,
        |((fibrePos X a).card : ℤ) - ((fibreNeg X a).card : ℤ)| : ℤ)) : ℝ) := by
    have hsub_sum : ∑ b ∈ B_roots, |((fibrePos X b).card : ℤ) - ((fibreNeg X b).card : ℤ)| ≤
        ∑ a ∈ balancedFibreClass X, |((fibrePos X a).card : ℤ) - ((fibreNeg X a).card : ℤ)| :=
      sum_le_sum_of_subset_of_nonneg hsub_roots fun _ _ _ => abs_nonneg _
    have hsub_sum_r :
        (((∑ b ∈ B_roots, |((fibrePos X b).card : ℤ) - ((fibreNeg X b).card : ℤ)| : ℤ)) : ℝ) ≤
        (((∑ a ∈ balancedFibreClass X,
          |((fibrePos X a).card : ℤ) - ((fibreNeg X a).card : ℤ)| : ℤ)) : ℝ) := by
      exact_mod_cast hsub_sum
    refine le_trans ?_ hsub_sum_r
    rw [Int.cast_sum]
    calc c₁ * (X : ℝ) / Real.log X ^ (3 : ℕ)
        = (c_fib * (X : ℝ) ^ (1 / 3 : ℝ) / Real.log X ^ (2 : ℕ)) *
            ((1 / 1000) * z ^ 120 / Real.log X) := by
          rw [← hz60, ← hz180]; dsimp [c₁]; ring
      _ ≤ ((B_roots.card : ℝ)) * ((1 / 1000) * z ^ 120 / Real.log X) :=
          mul_le_mul_of_nonneg_right hroot_card_lo
            (div_nonneg (mul_nonneg (by norm_num) (pow_nonneg hz0.le 120)) hLX.le)
      _ = ∑ _b ∈ B_roots, ((1 / 1000) * z ^ 120 / Real.log X) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ b ∈ B_roots, ((|((fibrePos X b).card : ℤ) - ((fibreNeg X b).card : ℤ)| : ℤ) : ℝ) :=
          sum_le_sum fun b hb => ((hcluster_main b hb).2.2.1).trans
            (by rw [Int.cast_abs]; push_cast; exact le_abs_self _)
  have hord_sum_hi :
      (((∑ a ∈ balancedFibreClass X,
        |((fibrePos X a).card : ℤ) - ((fibreNeg X a).card : ℤ)| : ℤ)) : ℝ) ≤
        c₂ * (X : ℝ) / Real.log X ^ (3 : ℕ) := by
    rw [← hcover_cof, sum_biUnion hdisj_cof, Int.cast_sum]
    calc ∑ b ∈ B_roots,
            (((∑ a ∈ clusterCofactors b,
              |((fibrePos X a).card : ℤ) - ((fibreNeg X a).card : ℤ)| : ℤ)) : ℝ)
        ≤ ∑ _b ∈ B_roots, ((1 / 5) * z ^ 120 / Real.log X) :=
          sum_le_sum fun b hb => (hcluster_main b hb).2.2.2.1
      _ = (B_roots.card : ℝ) * ((1 / 5) * z ^ 120 / Real.log X) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ (100 * z ^ 60 / Real.log X ^ (2 : ℕ)) * ((1 / 5) * z ^ 120 / Real.log X) :=
          mul_le_mul_of_nonneg_right hroot_card_hi
            (div_nonneg (mul_nonneg (by norm_num) (pow_nonneg hz0.le 120)) hLX.le)
      _ = c₂ * (X : ℝ) / Real.log X ^ (3 : ℕ) := by
          rw [← hz180]; dsimp [c₂]; ring
  -- 3. Glue the balanced involutions across `B_roots`
  let fam : ∀ b : ℕ, FactorizationInvolution GlobalDyadicOneTwoRel (clusterVerts b) := fun b =>
    if hb : b ∈ B_roots then (hcluster_main b hb).2.2.2.2.choose
    else
      { toFun := id
        involutive := fun _ => rfl
        fixed_outside := fun _ _ => rfl
        sign_flip := fun _ h => False.elim (h rfl)
        adj_pos := fun _ h _ => False.elim (h rfl) }
  let τ_glob := FactorizationInvolution.glueDisjoint B_roots clusterVerts hdisj_verts
    (fun _ hb => hcover_verts ▸ subset_biUnion_of_mem clusterVerts hb) fam
  have hτ_glob_unm : (τ_glob.unmatchedSet.card : ℝ) ≤ 4 * (X : ℝ) ^ (113 / 180 : ℝ) := by
    have hunm_eq := FactorizationInvolution.glueDisjoint_unmatchedSet_eq_biUnion
      B_roots clusterVerts hdisj_verts hcover_verts fam
    have hcard_le : τ_glob.unmatchedSet.card ≤ ∑ b ∈ B_roots, (fam b).unmatchedSet.card := by
      change (FactorizationInvolution.glueDisjoint _ _ _ _ _).unmatchedSet.card ≤ _
      rw [hunm_eq]
      exact card_biUnion_le
    refine (Nat.cast_le.mpr hcard_le).trans ?_
    rw [Nat.cast_sum]
    calc ∑ b ∈ B_roots, ((fam b).unmatchedSet.card : ℝ)
        ≤ ∑ _b ∈ B_roots, (4 * z ^ 53) := by
          refine sum_le_sum fun b hb => ?_
          simp only [fam, dif_pos hb]
          exact (hcluster_main b hb).2.2.2.2.choose_spec
      _ = (B_roots.card : ℝ) * (4 * z ^ 53) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ z ^ 60 * (4 * z ^ 53) :=
          mul_le_mul_of_nonneg_right hroot_card_triv
            (mul_nonneg (by norm_num) (pow_nonneg hz0.le 53))
      _ = 4 * (X : ℝ) ^ (113 / 180 : ℝ) := by rw [← hz113]; ring
  have h113_le_23 : (X : ℝ) ^ (113 / 180 : ℝ) ≤ (X : ℝ) ^ (2 / 3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith only [hX64]) (by norm_num)
  have habs_sum_le : |(∑ n ∈ fibreUnion X (balancedFibreClass X), μ n : ℝ)| ≤
      4 * (X : ℝ) ^ (113 / 180 : ℝ) := by
    have h1 : |∑ n ∈ fibreUnion X (balancedFibreClass X), μ n| ≤ (τ_glob.unmatchedSet.card : ℤ) :=
      τ_glob.abs_sum_moebius_le_unmatched
    have h1_r : |(∑ n ∈ fibreUnion X (balancedFibreClass X), μ n : ℝ)| ≤
        (τ_glob.unmatchedSet.card : ℝ) := by exact_mod_cast h1
    exact h1_r.trans hτ_glob_unm
  refine ⟨hcard_class_ge, fun τ₀ => hord_sum_lo.trans (by exact_mod_cast hord_lo_all τ₀),
    ⟨τ_ord, (show (τ_ord.unmatchedSet.card : ℝ) = _ by exact_mod_cast hτ_ord_eq).trans_le hord_sum_hi⟩,
    ⟨τ_glob, hτ_glob_unm,
      hτ_glob_unm.trans (mul_le_mul_of_nonneg_left h113_le_23 (by norm_num)),
      habs_sum_le⟩⟩

end GaloisForLFunctions.QuantitativeFactorizationMatching

