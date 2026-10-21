import GaloisForLFunctions.SquareRootThreshold.ZetaIsolatedTwinsCannotHide

/-!
# Coherent cores add up

`ZetaIsolatedTwinsCannotHide` shows that a tight companion adds to its record. The same holds for a
whole core of tight companions, also after the loose members of the cluster have been eliminated
across the Fejér orders. These are the tools for removing the cluster alternative altogether.

* **Coherent sums** (`norm_sum_coherent_ge`). If `Re(D_c D̄*) ≥ 0` on a finite set `C ∋ z*` and the
  weights satisfy `|ω_c − 1| ≤ η`, then `|Σ_C D_c ω_c| ≥ |D*| − η Σ_C |D_c|`.
* **Scales** (`exists_empty_annulus`). Among `P + 1` nested annuli `ρ/G^{j+1} < |z − z*| ≤ ρ/G^j` one
  is empty for at most `P` points: the cluster splits into a core of radius `ρ/G^{j+1}` and loose
  members beyond `ρ/G^j`, with the gap factor `G`.
* **Products** (`norm_prod_sub_prod_le`). Factors close in relative size `t` give products close in
  relative size `(1 + t)^{|S|} − 1`.
* **Partial elimination** (`zeta_partial_elimination_le`). Eliminating a part `S_L` of the cluster
  through the orders `k, …, k + |S_L|` leaves
  `|Σ_{z ∈ S ∖ S_L} D(z) Π_{y ∈ S_L}(x_y² − x_z²) K_{k+|S_L|}(x_z)|` at the noise level
  `(2(k+p))!(π/V)^{2(k+p)}(8/3)^p(4/3)^k Ξ/r^{2k+1}`.
* **The core survives** (`norm_mul_sub_mul_le`, `norm_core_sum_ge`). If the eliminated factors and
  the kernels of the core members are within relative error `η` of those of the record and the core
  is coherent, the eliminated core sum is at least `|F*| K(θ) |D*|/2`.

Across a gap `G` the factor `x_y² − x_c²` of a loose member `y` changes by `|θ² − x_c²| ≤ ρ₀(2θ + ρ₀)`
over the core, against `|x_y² − θ²| = |y − z*||x_y + θ| ≥ Gρ₀ ε_m`; a large gap makes the eliminated
factors coherent over the core.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-- **A coherent core adds up.** If every `D_c`, `c ∈ C`, has `Re(D_c D̄*) ≥ 0`, `z* ∈ C`, and the
weights satisfy `|ω_c − 1| ≤ η`, then `|Σ_c D_c ω_c| ≥ |D*| − η Σ_c |D_c|`. -/
theorem norm_sum_coherent_ge {C : Finset ℂ} {z₁ : ℂ} (hz₁ : z₁ ∈ C) (D ω : ℂ → ℂ) {η : ℝ}
    (hcoh : ∀ c ∈ C, 0 ≤ (D c * conj (D z₁)).re) (hω : ∀ c ∈ C, ‖ω c - 1‖ ≤ η) :
    ‖D z₁‖ - η * ∑ c ∈ C, ‖D c‖ ≤ ‖∑ c ∈ C, D c * ω c‖ := by
  classical
  -- the unweighted sum
  have hsum : ‖D z₁‖ ≤ ‖∑ c ∈ C, D c‖ := by
    rcases eq_or_ne (D z₁) 0 with h0 | h0
    · rw [h0, norm_zero]; exact norm_nonneg _
    have hD0 : 0 < ‖D z₁‖ := norm_pos_iff.mpr h0
    have hre : ‖D z₁‖ ^ 2 ≤ ((∑ c ∈ C, D c) * conj (D z₁)).re := by
      rw [Finset.sum_mul, Complex.re_sum, ← Finset.add_sum_erase _ _ hz₁]
      have h1 : (D z₁ * conj (D z₁)).re = ‖D z₁‖ ^ 2 := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
      have h2 : 0 ≤ ∑ c ∈ C.erase z₁, (D c * conj (D z₁)).re :=
        Finset.sum_nonneg fun c hc => hcoh c (Finset.mem_of_mem_erase hc)
      linarith
    have h3 : ((∑ c ∈ C, D c) * conj (D z₁)).re ≤ ‖∑ c ∈ C, D c‖ * ‖D z₁‖ := by
      refine (Complex.re_le_norm _).trans (le_of_eq ?_)
      rw [norm_mul, Complex.norm_conj]
    nlinarith
  have hsplit : ∑ c ∈ C, D c * ω c = ∑ c ∈ C, D c + ∑ c ∈ C, D c * (ω c - 1) := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun c _ => by ring
  have hrest : ‖∑ c ∈ C, D c * (ω c - 1)‖ ≤ η * ∑ c ∈ C, ‖D c‖ := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun c hc => ?_
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hω c hc) (norm_nonneg _)
  rw [hsplit]
  have := norm_sub_norm_le (∑ c ∈ C, D c) (-(∑ c ∈ C, D c * (ω c - 1)))
  rw [sub_neg_eq_add, norm_neg] at this
  linarith

/-- **An empty annulus.** For at most `P` points, `ρ > 0` and `G ≥ 1`, some `j ≤ P` leaves the annulus
`ρ/G^{j+1} < |z − z*| ≤ ρ/G^j` empty. -/
theorem exists_empty_annulus (T : Finset ℂ) (z₁ : ℂ) {P : ℕ} (hP : T.card ≤ P) {ρ G : ℝ}
    (hρ : 0 < ρ) (hG : 1 ≤ G) :
    ∃ j : ℕ, j ≤ P ∧ ∀ z ∈ T, ‖z - z₁‖ ≤ ρ / G ^ (j + 1) ∨ ρ / G ^ j < ‖z - z₁‖ := by
  classical
  set bad : ℂ → Finset ℕ := fun z => (Finset.range (P + 1)).filter fun j =>
    ρ / G ^ (j + 1) < ‖z - z₁‖ ∧ ‖z - z₁‖ ≤ ρ / G ^ j with hbad
  have hG0 : 0 < G := by linarith
  have hanti : ∀ i j : ℕ, i < j → ρ / G ^ j ≤ ρ / G ^ (i + 1) := fun i j hij =>
    div_le_div_of_nonneg_left hρ.le (by positivity) (pow_le_pow_right₀ hG (by omega))
  have hone : ∀ z, (bad z).card ≤ 1 := fun z => by
    rw [Finset.card_le_one]
    intro i hi j hj
    rw [hbad, Finset.mem_filter] at hi hj
    by_contra hij
    rcases lt_or_gt_of_ne hij with h | h
    · have := hanti i j h; linarith [hi.2.1, hj.2.2]
    · have := hanti j i h; linarith [hj.2.1, hi.2.2]
  have hcard : (T.biUnion bad).card < (Finset.range (P + 1)).card := by
    calc (T.biUnion bad).card ≤ ∑ z ∈ T, (bad z).card := Finset.card_biUnion_le
      _ ≤ ∑ _z ∈ T, 1 := Finset.sum_le_sum fun z _ => hone z
      _ = T.card := by simp
      _ < (Finset.range (P + 1)).card := by rw [Finset.card_range]; omega
  obtain ⟨j, hj, hjb⟩ : ∃ j ∈ Finset.range (P + 1), j ∉ T.biUnion bad := by
    by_contra h
    push Not at h
    exact absurd (Finset.card_le_card (fun j hj => h j hj)) (not_le.mpr hcard)
  refine ⟨j, Nat.lt_succ_iff.mp (Finset.mem_range.mp hj), fun z hz => ?_⟩
  by_contra h
  push Not at h
  exact hjb (Finset.mem_biUnion.mpr ⟨z, hz, Finset.mem_filter.mpr ⟨hj, h.1, h.2⟩⟩)

/-- **Products of close factors.** If `|a_y − b_y| ≤ t |b_y|` on a finite set `S`, then
`|Π a_y − Π b_y| ≤ ((1 + t)^{|S|} − 1) |Π b_y|`. -/
theorem norm_prod_sub_prod_le (S : Finset ℂ) (a b : ℂ → ℂ) {t : ℝ} (ht : 0 ≤ t)
    (hab : ∀ y ∈ S, ‖a y - b y‖ ≤ t * ‖b y‖) :
    ‖∏ y ∈ S, a y - ∏ y ∈ S, b y‖ ≤ ((1 + t) ^ S.card - 1) * ‖∏ y ∈ S, b y‖ := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert y S hy ih =>
    rw [Finset.prod_insert hy, Finset.prod_insert hy, Finset.card_insert_of_notMem hy]
    have ih' := ih fun y' hy' => hab y' (Finset.mem_insert_of_mem hy')
    have hy' := hab y (Finset.mem_insert_self y S)
    set A := ∏ y ∈ S, a y
    set B := ∏ y ∈ S, b y
    have e : a y * A - b y * B = (a y - b y) * A + b y * (A - B) := by ring
    rw [e]
    have hA : ‖A‖ ≤ (1 + t) ^ S.card * ‖B‖ := by
      have := norm_sub_norm_le A B
      nlinarith [norm_nonneg B]
    have hpow : 1 ≤ (1 + t) ^ S.card := one_le_pow₀ (by linarith)
    calc ‖(a y - b y) * A + b y * (A - B)‖
        ≤ ‖a y - b y‖ * ‖A‖ + ‖b y‖ * ‖A - B‖ := by
          refine (norm_add_le _ _).trans ?_; rw [norm_mul, norm_mul]
      _ ≤ t * ‖b y‖ * ((1 + t) ^ S.card * ‖B‖) + ‖b y‖ * (((1 + t) ^ S.card - 1) * ‖B‖) :=
          add_le_add (mul_le_mul hy' hA (norm_nonneg _) (by positivity))
            (mul_le_mul_of_nonneg_left ih' (norm_nonneg _))
      _ = ((1 + t) ^ (S.card + 1) - 1) * (‖b y‖ * ‖B‖) := by ring
      _ = ((1 + t) ^ (S.card + 1) - 1) * ‖b y * B‖ := by rw [norm_mul]

/-! ### Partial elimination -/

/-- **Partial elimination.** Under the hypotheses of `zeta_cluster_collapse`, eliminate a subset
`S_L ⊆ S` of the cluster not containing the record. The surviving members satisfy
`|Σ_{z ∈ S ∖ S_L} D(z) Π_{y ∈ S_L}(x_y² − x_z²) K_{k+p}(x_z)| ≤ (2(k+p))!(π/V)^{2(k+p)} (8/3)^p (4/3)^k Ξ/r^{2k+1}`,
`p = |S_L|`, `x_z = z − s`. -/
theorem zeta_partial_elimination_le {b : ℝ → ℂ} (hb : ContDiff ℝ 2 b) {w : ℝ}
    (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {V : ℝ}
    (hm : ∀ v ∈ Icc (0 : ℝ) V, 0 ≤ (zetaZeroConfig.W (twoBump b v (-1)) (twoBump b v (-1))).re)
    {z₁ : ℂ} (hz₁ : evenCoeff zetaZeroConfig b z₁ ≠ 0)
    (hrec : ∀ z : ℂ, evenCoeff zetaZeroConfig b z ≠ 0 → 0 < z.re →
      ‖evenCoeff zetaZeroConfig b z‖ * Real.exp (z.re * V) ≤
        ‖evenCoeff zetaZeroConfig b z₁‖ * Real.exp (z₁.re * V))
    {κ r : ℝ} (hκ : 0 < κ) (hr : 0 < r) (hr1 : r ≤ 1) (hrσ : r ≤ z₁.re - κ / V) {k : ℕ}
    (hk : 1 ≤ k) (S SL : Finset ℂ) (hSL : SL ⊆ S)
    (hSr : ∀ z ∈ S, ‖z - ((z₁.re - κ / V : ℝ) + z₁.im * I)‖ ≤ r)
    (hiso : ∀ z, z ∉ S → evenCoeff zetaZeroConfig b z ≠ 0 →
      r ≤ ‖z - ((z₁.re - κ / V : ℝ) + z₁.im * I)‖)
    (hV : π * (k + SL.card : ℕ) ≤ V) (hVr : 4 * π * (k + SL.card : ℕ) ≤ V * r) :
    ‖∑ z ∈ S.filter (fun z => z ∉ SL), evenCoeff zetaZeroConfig b z *
        (∏ y ∈ SL, ((y - ((z₁.re - κ / V : ℝ) + z₁.im * I)) ^ 2 -
          (z - ((z₁.re - κ / V : ℝ) + z₁.im * I)) ^ 2)) *
        fejerPowWin (k + SL.card) V (z - ((z₁.re - κ / V : ℝ) + z₁.im * I))‖ ≤
      (2 * (k + SL.card)).factorial * (π / V) ^ (2 * (k + SL.card)) *
        ((8 / 3) ^ SL.card * (4 / 3) ^ k *
          (4 * |2 * (lagStructure zetaZeroConfig b 0).re| +
            4 * (∑' z : ℂ, ‖evenCoeff zetaZeroConfig b z‖) +
            3840 * Real.log (180 * (|z₁.im| + 6)) * ‖evenCoeff zetaZeroConfig b z₁‖ *
              Real.exp κ) / r ^ (2 * k + 1)) := by
  classical
  set D := evenCoeff zetaZeroConfig b with hDdef
  set s : ℂ := ((z₁.re - κ / V : ℝ) : ℂ) + z₁.im * I with hs
  set p := SL.card with hp
  set M : ℝ := 2 * (lagStructure zetaZeroConfig b 0).re with hM
  set W : ℝ := ∑' z : ℂ, ‖D z‖ with hW
  set L : ℝ := Real.log (180 * (|z₁.im| + 6)) with hL
  set Ξ : ℝ := 4 * |M| + 4 * W + 3840 * L * ‖D z₁‖ * Real.exp κ with hΞ
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hV0 : 0 < V := lt_of_lt_of_le (by positivity) hV
  have hW0 : 0 ≤ W := tsum_nonneg fun z => norm_nonneg _
  have hL0 : 0 ≤ L := Real.log_nonneg (by nlinarith [abs_nonneg z₁.im])
  have hΞ0 : 0 ≤ Ξ := by rw [hΞ]; positivity
  have hσ : 0 < z₁.re - κ / V := lt_of_lt_of_le hr hrσ
  set x : ℂ → ℂ := fun z => z - s with hx
  have hA : ∀ m' : ℕ, k ≤ m' → m' ≤ k + p → ‖elimSeq V S D x [] m'‖ ≤
      (2 * m').factorial * (π / V) ^ (2 * m') * ((4 / 3) ^ m' * Ξ / r ^ (2 * m' + 1)) := by
    intro m' h1 h2
    have hm1 : 1 ≤ m' := le_trans hk h1
    have hm'r : (m' : ℝ) ≤ (k + p : ℕ) := by exact_mod_cast h2
    have hcl := zeta_powCluster_le hb hbs (j := m') hm1 (by nlinarith [Real.pi_pos]) hm hz₁ hrec hκ
      hσ hr (by linarith) (by nlinarith [Real.pi_pos]) S hiso
    have hbr := clusterBracket_le (j := m') hm1 (M := M) (W := W) (D := ‖D z₁‖) (κ := κ) z₁.im hW0
      (norm_nonneg _) hr hr1 hrσ
    have e : elimSeq V S D x [] m' = ∑ z ∈ S, D z * fejerPowWin m' V (z - s) := by
      simp [elimSeq, hx]
    rw [e]
    refine hcl.trans ?_
    refine mul_le_mul_of_nonneg_left (le_trans (le_of_eq ?_) hbr) (by positivity)
    rfl
  set ys : List ℂ := SL.toList.map fun z => x z ^ 2 with hys
  have hlen : ys.length = p := by rw [hys, List.length_map, Finset.length_toList]
  have hysr : ∀ y ∈ ys, ‖y‖ ≤ r ^ 2 := by
    intro y hy
    rw [hys, List.mem_map] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    rw [Finset.mem_toList] at hz
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hSr z (hSL hz)) 2
  have hΦ := norm_elimSeq_le hV0 hr hΞ0 S D x ys k hysr (by rw [hlen]; exact hVr)
    (fun m' h1 h2 => hA m' h1 (by rw [hlen] at h2; exact h2))
  rw [hlen] at hΦ
  have hprod : ∀ z, ((SL.toList.map fun z => x z ^ 2).map fun y => y - x z ^ 2).prod =
      ∏ z' ∈ SL, (x z' ^ 2 - x z ^ 2) := fun z => by
    rw [List.map_map]; exact Finset.prod_map_toList _ _
  have hval : elimSeq V S D x ys k = ∑ z ∈ S.filter (fun z => z ∉ SL),
      D z * (∏ y ∈ SL, (x y ^ 2 - x z ^ 2)) * fejerPowWin (k + p) V (x z) := by
    unfold elimSeq
    rw [hlen, hys]
    simp_rw [hprod]
    rw [← Finset.sum_filter_add_sum_filter_not S (fun z => z ∈ SL)]
    have h0 : ∑ z ∈ S.filter (fun z => z ∈ SL),
        D z * (∏ z' ∈ SL, (x z' ^ 2 - x z ^ 2)) * fejerPowWin (k + p) V (x z) = 0 :=
      Finset.sum_eq_zero fun z hz => by
        have : ∏ z' ∈ SL, (x z' ^ 2 - x z ^ 2) = 0 :=
          Finset.prod_eq_zero (f := fun z' => x z' ^ 2 - x z ^ 2) (Finset.mem_filter.mp hz).2
            (sub_self _)
        rw [this, mul_zero, zero_mul]
    rw [h0, zero_add]
  rw [hval] at hΦ
  exact hΦ

/-! ### The coherent core after elimination -/

/-- `|F K − F₁ t| ≤ ((1 + τ)·2ρV + τ)|F₁| t` from `|F − F₁| ≤ τ|F₁|` and `|K − t| ≤ 2ρV t`. -/
theorem norm_mul_sub_mul_le {F F₁ K : ℂ} {t τ ρV : ℝ} (ht : 0 ≤ t) (hτ : 0 ≤ τ)
    (hF : ‖F - F₁‖ ≤ τ * ‖F₁‖) (hK : ‖K - t‖ ≤ 2 * ρV * t) :
    ‖F * K - F₁ * t‖ ≤ ((1 + τ) * (2 * ρV) + τ) * ‖F₁‖ * t := by
  have e : F * K - F₁ * t = F * (K - t) + (F - F₁) * t := by ring
  rw [e]
  have hFn : ‖F‖ ≤ (1 + τ) * ‖F₁‖ := by
    have := norm_sub_norm_le F F₁; nlinarith [norm_nonneg F₁]
  have hρV : 0 ≤ 2 * ρV * t := (norm_nonneg _).trans hK
  calc ‖F * (K - t) + (F - F₁) * t‖ ≤ ‖F‖ * ‖K - t‖ + ‖F - F₁‖ * t := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
    _ ≤ (1 + τ) * ‖F₁‖ * (2 * ρV * t) + τ * ‖F₁‖ * t :=
        add_le_add (mul_le_mul hFn hK (norm_nonneg _) (by positivity))
          (mul_le_mul_of_nonneg_right hF ht)
    _ = ((1 + τ) * (2 * ρV) + τ) * ‖F₁‖ * t := by ring

/-- **The eliminated core keeps the record.** If the members `c` of a finite set `C ∋ z*` are
coherent with the record (`Re(D_c D̄*) ≥ 0`) and `|F_c K_c − F* t| ≤ η |F*| t` with `F* ≠ 0`, `t > 0`,
`η Σ_C |D_c| ≤ |D*|/2`, then `|Σ_C D_c F_c K_c| ≥ |F*| t |D*|/2`. -/
theorem norm_core_sum_ge {C : Finset ℂ} {z₁ : ℂ} (hz₁ : z₁ ∈ C) (D F K : ℂ → ℂ) {t η : ℝ}
    (ht : 0 < t) (hF₁ : F z₁ ≠ 0)
    (hcoh : ∀ c ∈ C, 0 ≤ (D c * conj (D z₁)).re)
    (hFK : ∀ c ∈ C, ‖F c * K c - F z₁ * t‖ ≤ η * ‖F z₁‖ * t)
    (hη : η * ∑ c ∈ C, ‖D c‖ ≤ ‖D z₁‖ / 2) :
    ‖F z₁‖ * t * ‖D z₁‖ / 2 ≤ ‖∑ c ∈ C, D c * F c * K c‖ := by
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hFt : F z₁ * (t : ℂ) ≠ 0 := mul_ne_zero hF₁ ht0
  have hFtn : ‖F z₁ * (t : ℂ)‖ = ‖F z₁‖ * t := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  set ω : ℂ → ℂ := fun c => F c * K c / (F z₁ * t) with hω
  have hω1 : ∀ c ∈ C, ‖ω c - 1‖ ≤ η := fun c hc => by
    have e : ω c - 1 = (F c * K c - F z₁ * t) / (F z₁ * t) := by
      rw [hω]; field_simp
    rw [e, norm_div, hFtn, div_le_iff₀ (by positivity)]
    have := hFK c hc; linarith
  have hsum := norm_sum_coherent_ge hz₁ D ω hcoh hω1
  have e : ∑ c ∈ C, D c * F c * K c = (F z₁ * t) * ∑ c ∈ C, D c * ω c := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hω]; field_simp
  rw [e, norm_mul, hFtn]
  have h1 : ‖D z₁‖ / 2 ≤ ‖∑ c ∈ C, D c * ω c‖ := by linarith
  have h2 : 0 ≤ ‖F z₁‖ * t := by positivity
  calc ‖F z₁‖ * t * ‖D z₁‖ / 2 = ‖F z₁‖ * t * (‖D z₁‖ / 2) := by ring
    _ ≤ ‖F z₁‖ * t * ‖∑ c ∈ C, D c * ω c‖ := mul_le_mul_of_nonneg_left h1 h2

end GaloisForLFunctions.SquareRootThreshold
