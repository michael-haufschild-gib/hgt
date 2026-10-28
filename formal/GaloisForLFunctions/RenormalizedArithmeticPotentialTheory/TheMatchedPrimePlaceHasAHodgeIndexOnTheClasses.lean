import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheArchimedeanPlacePaysTheTowerDeficit

/-!
# The matched prime place has a Hodge index on the classes

Raw, the prime kernel on a ladder `1, p, …, p⁵` carries two positive squares
(`LocalFactorsAndTheEulerProductClosure`): there is no local Lorentzian structure at a prime.
Matched against the archimedean counterterm `log M − γ` instead, the prime form on the span of the
`p`-adic class pole vectors has exactly the signature of a Hodge index: one positive direction, the
pole, and a uniform gap below it on the polar hyperplane.

* **The valuation inequality with its Dirichlet remainder** (`sum_cross_add_gap_le_valuation`): for
  masses with `m_{j+1} ≤ m_j/p`,
  `Σ_{j ≠ j'} a_j a_{j'} m_{max} + (S Σ_j m_j a_j² − (Σ_j m_j a_j)²)/m_0 ≤ Σ_j a_j² m_j (j + 1/(p − 1))`,
  `S = Σ_j m_j`. The Metzler stability identity keeps the Laplacian `½ Σ m_{max}(a_j − a_{j'})²`, and
  `m_{max} ≥ m_j m_{j'}/m_0`.
* **The polar functional of a class combination** (`polarFunctional_classCombination`):
  `ℓ(Σ a_j w_j) = Σ_j a_j |w_j|²`.
* **The gap** (`eventually_atomicWeilForm_classCombination_gap_le`): with `g_J = Σ_{j ≤ J} p^{−j}`,
  eventually in `M`,
  `P_M(x) + (g_J − η) log p |x|² ≤ (log M − γ + η)|x|² + (log p/|w_0|²) ℓ(x)²`.
  On the polar hyperplane `ℓ(x) = 0`: `P_M(x) ≤ (log M − γ − g_J log p + 2η)|x|²`.
* **Hodge index** (`eventually_isHyperbolic_classHodgeGram`): for `0 < η ≤ min(1/2, log p/4)`,
  eventually the Gram of `P_M − (log M − γ − η)|·|²` on the class pole vectors of depth `≤ J` has at
  most one positive square; the pole vector carries it (`eventually_atomicWeilForm_truncPole_ge`).

As `J → ∞` the gap tends to `p log p/(p − 1)`, the first excitation of the valuation tower operator
`diag(j log p) + γ_p + log p − log p K_{p^{−1/2}}` above its ground energy `γ`; it is smallest at
`p = 2`, where it equals `2 log 2`.
-/

noncomputable section

open Filter Topology Finset Matrix

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open GaloisForLFunctions.ArithmeticIntersectionTheory GaloisForLFunctions.ArithmeticElectrostatics
  GaloisForLFunctions.ArithmeticLorentzianGeometry

local notation "γ" => Real.eulerMascheroniConstant

variable {p J : ℕ} {m : ℕ → ℝ}

/-! ### 1. The valuation inequality with its Dirichlet remainder -/

/-- Descending masses are dominated by the top one. -/
theorem le_zero_of_desc (hp : 1 < (p : ℝ)) (hm0 : ∀ j, 0 ≤ m j) (hm : ∀ j, m (j + 1) ≤ m j / p)
    (j : ℕ) : m j ≤ m 0 := by
  induction j with
  | zero => exact le_rfl
  | succ j ih =>
    have h := hm j
    have : m j / p ≤ m j := div_le_self (hm0 j) hp.le
    linarith

/-- The gram identity `½ Σ_{j,k} m_j m_k (a_j − a_k)² = S Σ m_j a_j² − (Σ m_j a_j)²`. -/
theorem half_sum_mul_sq_sub (a w : Fin (J + 1) → ℝ) :
    (1 / 2) * ∑ j, ∑ k, w j * w k * (a j - a k) ^ 2 =
      (∑ j, w j) * ∑ j, w j * a j ^ 2 - (∑ j, w j * a j) ^ 2 := by
  have A : ∑ j, ∑ k, w j * a j ^ 2 * w k = (∑ j, w j * a j ^ 2) * ∑ k, w k := by
    rw [sum_mul]; exact sum_congr rfl fun j _ => by rw [mul_sum]
  have B : ∑ j, ∑ k, w j * (w k * a k ^ 2) = (∑ j, w j) * ∑ k, w k * a k ^ 2 := by
    rw [sum_mul]; exact sum_congr rfl fun j _ => by rw [mul_sum]
  have Cc : ∑ j, ∑ k, w j * a j * (w k * a k) = (∑ j, w j * a j) * ∑ k, w k * a k := by
    rw [sum_mul]; exact sum_congr rfl fun j _ => by rw [mul_sum]
  have h : ∀ j, ∑ k, w j * w k * (a j - a k) ^ 2 = ∑ k, w j * a j ^ 2 * w k +
      ∑ k, w j * (w k * a k ^ 2) - 2 * ∑ k, w j * a j * (w k * a k) := fun j => by
    rw [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    exact sum_congr rfl fun k _ => by ring
  rw [sum_congr rfl fun j _ => h j, sum_sub_distrib, sum_add_distrib, ← mul_sum, A, B, Cc]
  ring

/-- **The valuation inequality with its Dirichlet remainder.** -/
theorem sum_cross_add_gap_le_valuation (hp : 1 < (p : ℝ)) (hm0 : ∀ j, 0 ≤ m j)
    (hm : ∀ j, m (j + 1) ≤ m j / p) (htop : 0 < m 0) (a : Fin (J + 1) → ℝ) :
    ∑ j : Fin (J + 1), ∑ j' : Fin (J + 1),
        (if j = j' then 0 else a j * a j' * m (max (j : ℕ) j')) +
      ((∑ j : Fin (J + 1), m j) * ∑ j : Fin (J + 1), m j * a j ^ 2 -
          (∑ j : Fin (J + 1), m j * a j) ^ 2) / m 0 ≤
      ∑ j : Fin (J + 1), a j ^ 2 * (m j * ((j : ℝ) + 1 / ((p : ℝ) - 1))) := by
  set G := valuationGram p J m
  have hG := valuationGram_isSymm (p := p) (J := J) (m := m)
  -- the stability identity with the Laplacian kept
  have hid := sum_rowSum_mul_sq_sub_qf hG a
  have hrow : ∑ j, rowSum G j * a j ^ 2 ≤ 0 := sum_nonpos fun j _ =>
    mul_nonpos_of_nonpos_of_nonneg (valuationGram_mulVec_one_nonpos hp hm0 hm j) (sq_nonneg _)
  -- the Laplacian dominates the complete graph with weights `m_j m_k / m_0`
  have hlap : (1 / 2) * ∑ j : Fin (J + 1), ∑ k : Fin (J + 1),
      (m j / m 0) * m k * (a j - a k) ^ 2 ≤
      (1 / 2) * ∑ j, ∑ k, G j k * (a j - a k) ^ 2 := by
    refine mul_le_mul_of_nonneg_left (sum_le_sum fun j _ => sum_le_sum fun k _ => ?_) (by norm_num)
    by_cases hjk : j = k
    · subst hjk; simp
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    simp only [G, valuationGram, if_neg hjk]
    rw [div_mul_eq_mul_div, div_le_iff₀ htop]
    rcases le_total (j : ℕ) k with h | h
    · rw [max_eq_right h]
      calc m j * m k ≤ m 0 * m k :=
            mul_le_mul_of_nonneg_right (le_zero_of_desc hp hm0 hm j) (hm0 _)
        _ = m k * m 0 := mul_comm _ _
    · rw [max_eq_left h]
      exact mul_le_mul_of_nonneg_left (le_zero_of_desc hp hm0 hm k) (hm0 _)
  have hgram := half_sum_mul_sq_sub a (fun j => m j)
  have hgram' : (1 / 2) * ∑ j : Fin (J + 1), ∑ k : Fin (J + 1),
      (m j / m 0) * m k * (a j - a k) ^ 2 =
      ((∑ j : Fin (J + 1), m j) * ∑ j : Fin (J + 1), m j * a j ^ 2 -
          (∑ j : Fin (J + 1), m j * a j) ^ 2) / m 0 := by
    rw [← hgram, mul_div_assoc, sum_div]
    congr 1
    refine sum_congr rfl fun j _ => ?_
    rw [sum_div]
    exact sum_congr rfl fun k _ => by field_simp
  -- the quadratic form of the valuation Gram
  have hrow' : ∀ j : Fin (J + 1), ∑ j', G j j' * a j' =
      ∑ j', (if j = j' then 0 else m (max (j : ℕ) j') * a j') -
        m j * ((j : ℝ) + 1 / ((p : ℝ) - 1)) * a j := by
    intro j
    have h : ∀ j', G j j' * a j' =
        (if j = j' then 0 else m (max (j : ℕ) j') * a j') +
          (if j = j' then -(m j * ((j : ℝ) + 1 / ((p : ℝ) - 1)) * a j') else 0) := by
      intro j'
      by_cases h : j = j'
      · subst h; simp [G, valuationGram]
      · simp [G, valuationGram, h]
    rw [sum_congr rfl fun j' _ => h j', sum_add_distrib, sum_ite_eq, if_pos (mem_univ j)]
    ring
  have hexp : qf G a =
      ∑ j : Fin (J + 1), ∑ j' : Fin (J + 1),
        (if j = j' then 0 else a j * a j' * m (max (j : ℕ) j')) -
      ∑ j : Fin (J + 1), a j ^ 2 * (m j * ((j : ℝ) + 1 / ((p : ℝ) - 1))) := by
    simp only [qf, bil, dotProduct, mulVec]
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun j _ => ?_
    rw [hrow' j, mul_sub, mul_sum]
    congr 1
    · refine sum_congr rfl fun j' _ => ?_
      split_ifs <;> ring
    · ring
  linarith

/-! ### 2. The polar functional of a class combination -/

/-- `ℓ(Σ_j a_j w_j^{(M)}) = Σ_j a_j |w_j^{(M)}|²`. -/
theorem polarFunctional_classCombination (a : Fin (J + 1) → ℝ) (M : ℕ) :
    polarFunctional M (fun n => ∑ j : Fin (J + 1), a j * classPole p j M n) =
      ∑ j : Fin (J + 1), a j * classMass p j M := by
  unfold polarFunctional classMass
  simp only [sum_mul, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun j _ => sum_congr rfl fun n hn => ?_
  have hn1 := (mem_Icc.mp hn).1
  have hnM := (mem_Icc.mp hn).2
  simp only [classPole, truncPole, poleVector, if_pos hnM]
  split_ifs
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    rw [mul_assoc, ← sq, div_pow, one_pow, Real.sq_sqrt hn0.le]
  · ring

/-! ### 3. The gap on the polar hyperplane -/

/-- The truncated tower mass `g_J = Σ_{j ≤ J} p^{−j}`. -/
def towerMass (p J : ℕ) : ℝ := ∑ j : Fin (J + 1), 1 / (p : ℝ) ^ (j : ℕ)

theorem one_le_towerMass : 1 ≤ towerMass p J := by
  unfold towerMass
  calc (1 : ℝ) = 1 / (p : ℝ) ^ ((0 : Fin (J + 1)) : ℕ) := by simp
    _ ≤ _ := single_le_sum (f := fun j : Fin (J + 1) => 1 / (p : ℝ) ^ (j : ℕ))
        (fun j _ => by positivity) (mem_univ _)

/-- The top class mass grows: `|w_0^{(M)}|² → ∞`. -/
theorem tendsto_classMass_zero_atTop (hp : p.Prime) :
    Tendsto (fun M : ℕ => classMass p 0 M) atTop atTop := by
  have ht := tendsto_classMass_sub hp 0
  have hδ := classDensity_pos hp 0
  have hlog : Tendsto (fun M : ℕ => classDensity p 0 * (Real.log M - ((0 : ℕ) : ℝ) * Real.log p +
      localEuler p) + (-1)) atTop atTop := by
    refine tendsto_atTop_add_const_right _ _ (Tendsto.const_mul_atTop hδ ?_)
    refine tendsto_atTop_add_const_right _ _ ?_
    simp only [Nat.cast_zero, zero_mul, sub_zero]
    exact Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine tendsto_atTop_mono' _ ?_ hlog
  filter_upwards [ht.eventually (lt_mem_nhds (by norm_num : (-1 : ℝ) < 0))] with M hM
  linarith

/-- The tower mass of the class masses: `Σ_{j ≤ J} |w_j|² ≥ (g_J − η) |w_0|²` eventually. -/
theorem eventually_sum_classMass_ge (hp : p.Prime) (J : ℕ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ M : ℕ in atTop,
      (towerMass p J - η) * classMass p 0 M ≤ ∑ j : Fin (J + 1), classMass p j M := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  -- `m_j − p^{−j} m_0 → −δ_j j log p`
  have hlim : ∀ j : ℕ, Tendsto (fun M : ℕ => classMass p j M - 1 / (p : ℝ) ^ j * classMass p 0 M)
      atTop (𝓝 (-(classDensity p j * (j * Real.log p)))) := by
    intro j
    have h1 := tendsto_classMass_sub hp j
    have h0 := (tendsto_classMass_sub hp 0).const_mul (1 / (p : ℝ) ^ j)
    have h := h1.sub h0
    rw [mul_zero, sub_zero] at h
    have h' := h.add_const (-(classDensity p j * (j * Real.log p)))
    rw [zero_add] at h'
    refine h'.congr fun M => ?_
    have hδ : classDensity p j = 1 / (p : ℝ) ^ j * classDensity p 0 := by
      unfold classDensity; rw [pow_zero, div_one]; ring
    rw [hδ]; push_cast; ring
  set c : ℝ := ∑ j : Fin (J + 1), -(classDensity p j * (j * Real.log p))
  have hS : Tendsto (fun M : ℕ => ∑ j : Fin (J + 1), classMass p j M -
      towerMass p J * classMass p 0 M) atTop (𝓝 c) := by
    have := tendsto_finsetSum (univ : Finset (Fin (J + 1))) fun j _ => hlim j
    refine this.congr fun M => ?_
    rw [towerMass, sum_mul, ← sum_sub_distrib]
  have h1 := hS.eventually (lt_mem_nhds (by linarith : c - 1 < c))
  have h2 := (tendsto_classMass_zero_atTop hp).eventually_ge_atTop ((1 - c) / η)
  filter_upwards [h1, h2] with M hM1 hM2
  rw [div_le_iff₀ hη] at hM2
  nlinarith

/-- **The gap on the polar hyperplane.** Eventually in `M`, every class combination of depth `≤ J`
satisfies `P_M(x) + (g_J − η) log p |x|² ≤ (log M − γ + η)|x|² + (log p/|w_0|²) ℓ(x)²`. -/
theorem eventually_atomicWeilForm_classCombination_gap_le (hp : p.Prime) (J : ℕ) {η : ℝ}
    (hη : 0 < η) :
    ∃ M₀ : ℕ, ∀ M, M₀ ≤ M → ∀ a : Fin (J + 1) → ℝ,
      atomicWeilForm M (fun n => ∑ j : Fin (J + 1), a j * classPole p j M n) +
          (towerMass p J - η) * Real.log p *
            ∑ n ∈ Icc 1 M, (∑ j : Fin (J + 1), a j * classPole p j M n) ^ 2 ≤
        (Real.log M - γ + η) *
            ∑ n ∈ Icc 1 M, (∑ j : Fin (J + 1), a j * classPole p j M n) ^ 2 +
          Real.log p / classMass p 0 M *
            polarFunctional M (fun n => ∑ j : Fin (J + 1), a j * classPole p j M n) ^ 2 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hlogp : 0 < Real.log p := Real.log_pos hp1
  obtain ⟨C, hC⟩ := exists_abs_atomicWeilForm_classCombination_finitePart_le hp J
    (η := η / 3) (by positivity)
  set C' : ℝ := max C 0
  have hev : ∀ j : Fin (J + 1), ∀ᶠ M : ℕ in atTop,
      classMass p j M ≤ classDensity p j * (Real.log M - j * Real.log p + localEuler p + η / 3) ∧
        3 * C' / η ≤ classMass p j M := by
    intro j
    have hδ := classDensity_pos hp j
    have ht := tendsto_classMass_sub hp j
    have h1 : ∀ᶠ M : ℕ in atTop, classMass p j M -
        classDensity p j * (Real.log M - j * Real.log p + localEuler p) <
          classDensity p j * (η / 3) :=
      ht.eventually (gt_mem_nhds (by positivity))
    have h2 : ∀ᶠ M : ℕ in atTop, -1 < classMass p j M -
        classDensity p j * (Real.log M - j * Real.log p + localEuler p) :=
      ht.eventually (lt_mem_nhds (by norm_num))
    have hlog : Tendsto (fun M : ℕ => classDensity p j * (Real.log M - j * Real.log p +
        localEuler p)) atTop atTop := by
      refine Tendsto.const_mul_atTop hδ ?_
      refine tendsto_atTop_add_const_right _ _ (tendsto_atTop_add_const_right _ _ ?_)
      exact Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have h3 := hlog.eventually_ge_atTop (3 * C' / η + 1)
    filter_upwards [h1, h2, h3] with M hM1 hM2 hM3
    exact ⟨by nlinarith, by linarith⟩
  have hgapev := eventually_sum_classMass_ge hp J hη
  have htop := (tendsto_classMass_zero_atTop hp).eventually_gt_atTop 0
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp ((eventually_all.mpr hev).and (hgapev.and htop))
  refine ⟨M₀, fun M hM a => ?_⟩
  obtain ⟨hmass, hgap, hm0pos⟩ := hM₀ M hM
  have hmm0 : ∀ j, 0 ≤ classMass p j M := fun j => classMass_nonneg p j M
  have hval := sum_cross_add_gap_le_valuation (J := J) hp1 hmm0
    (fun j => classMass_succ_le hp j M) hm0pos a
  rw [sum_classCombination_sq (p := p) a M, polarFunctional_classCombination a M]
  have hfin := hC M a
  have hdiag : ∀ j : Fin (J + 1), (a j * classMass p j M) ^ 2 / classDensity p j ≤
      a j ^ 2 * classMass p j M * (Real.log M - j * Real.log p + localEuler p + η / 3) := by
    intro j
    have hδ := classDensity_pos hp j
    rw [div_le_iff₀ hδ]
    have e : (a j * classMass p j M) ^ 2 = a j ^ 2 * classMass p j M * classMass p j M := by ring
    rw [e]
    calc a j ^ 2 * classMass p j M * classMass p j M
        ≤ a j ^ 2 * classMass p j M *
            (classDensity p j * (Real.log M - j * Real.log p + localEuler p + η / 3)) :=
          mul_le_mul_of_nonneg_left (hmass j).1 (mul_nonneg (sq_nonneg _) (hmm0 j))
      _ = _ := by ring
  have hC' : ∀ j : Fin (J + 1), a j ^ 2 * (η / 3 * classMass p j M + C) ≤
      a j ^ 2 * (2 * η / 3 * classMass p j M) := by
    intro j
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    have h1 : C ≤ C' := le_max_left _ _
    have h2 : 3 * C' / η ≤ classMass p j M := (hmass j).2
    have h3 : C' ≤ η / 3 * classMass p j M := by
      rw [div_le_iff₀ hη] at h2; linarith
    linarith
  have hD := sum_le_sum fun j (_ : j ∈ univ) => hdiag j
  have hE := sum_le_sum fun j (_ : j ∈ univ) => hC' j
  set S : ℝ := ∑ j : Fin (J + 1), a j ^ 2 * classMass p j M with hSdef
  set W : ℝ := ∑ j : Fin (J + 1), a j ^ 2 * classMass p j M * j
  set L : ℝ := ∑ j : Fin (J + 1), a j * classMass p j M
  set T : ℝ := ∑ j : Fin (J + 1), classMass p j M
  set X : ℝ := ∑ j : Fin (J + 1), ∑ j' : Fin (J + 1),
      (if j = j' then 0 else a j * a j' * classMass p (max (j : ℕ) j') M)
  have hsplit : ∑ j : Fin (J + 1), a j ^ 2 * classMass p j M *
      (Real.log M - j * Real.log p + localEuler p + η / 3) =
      (Real.log M + localEuler p + η / 3) * S - Real.log p * W := by
    rw [hSdef, mul_sum, mul_sum, ← sum_sub_distrib]; exact sum_congr rfl fun j _ => by ring
  have hS' : ∑ j : Fin (J + 1), classMass p j M * a j ^ 2 = S :=
    sum_congr rfl fun j _ => by ring
  have hR : ∑ j : Fin (J + 1), a j ^ 2 * (classMass p j M * ((j : ℝ) + 1 / ((p : ℝ) - 1))) =
      W + 1 / ((p : ℝ) - 1) * S := by
    rw [hSdef, mul_sum, ← sum_add_distrib]; exact sum_congr rfl fun j _ => by ring
  have hL' : ∑ j : Fin (J + 1), classMass p j M * a j = L := sum_congr rfl fun j _ => mul_comm _ _
  rw [hS', hR, hL'] at hval
  have hsum2 : ∑ j : Fin (J + 1), a j ^ 2 * (2 * η / 3 * classMass p j M) = 2 * η / 3 * S := by
    rw [hSdef, mul_sum]; exact sum_congr rfl fun j _ => by ring
  have habs := (abs_le.mp (hfin.trans (hsum2 ▸ hE))).2
  -- the gap term: `(T S − L²)/m_0 ≥ (g_J − η) S − L²/m_0`
  have hm0 := hm0pos
  have hTS : (towerMass p J - η) * S ≤ (T * S - L ^ 2) / classMass p 0 M + L ^ 2 / classMass p 0 M := by
    rw [← add_div, sub_add_cancel, le_div_iff₀ hm0]
    have hS0 : 0 ≤ S := sum_nonneg fun j _ => mul_nonneg (sq_nonneg _) (hmm0 j)
    nlinarith [mul_le_mul_of_nonneg_right hgap hS0]
  have hpot : Real.log p * ((T * S - L ^ 2) / classMass p 0 M) ≥
      Real.log p * ((towerMass p J - η) * S) - Real.log p / classMass p 0 M * L ^ 2 := by
    have := mul_le_mul_of_nonneg_left hTS hlogp.le
    rw [mul_add] at this
    have e : Real.log p * (L ^ 2 / classMass p 0 M) = Real.log p / classMass p 0 M * L ^ 2 := by
      ring
    linarith
  have hval2 := mul_le_mul_of_nonneg_left hval hlogp.le
  rw [mul_add, mul_add] at hval2
  unfold localEuler at hsplit habs hD
  have e2 : Real.log p * (1 / ((p : ℝ) - 1) * S) = Real.log p / ((p : ℝ) - 1) * S := by ring
  rw [e2] at hval2
  nlinarith [hD, hsplit, hval2, habs, hpot]

/-! ### 4. Hodge index -/

/-- The Gram of `P_M − c |·|²` on the class pole vectors of depth `≤ J`. -/
def classHodgeGram (p J M : ℕ) (c : ℝ) : Matrix (Fin (J + 1)) (Fin (J + 1)) ℝ :=
  fun j j' => primeBilinear M (classPole p j M) (classPole p j' M) -
    c * (if j = j' then classMass p j M else 0)

theorem classHodgeGram_isSymm (M : ℕ) (c : ℝ) : (classHodgeGram p J M c).IsSymm := by
  ext j j'
  simp only [Matrix.transpose_apply, classHodgeGram, primeBilinear_comm M (classPole p j' M)]
  by_cases h : j = j'
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h)]

theorem qf_classHodgeGram (M : ℕ) (c : ℝ) (a : Fin (J + 1) → ℝ) :
    qf (classHodgeGram p J M c) a =
      atomicWeilForm M (fun n => ∑ j : Fin (J + 1), a j * classPole p j M n) -
        c * ∑ n ∈ Icc 1 M, (∑ j : Fin (J + 1), a j * classPole p j M n) ^ 2 := by
  have hP : atomicWeilForm M (fun n => ∑ j : Fin (J + 1), a j * classPole p j M n) =
      ∑ j : Fin (J + 1), ∑ j' : Fin (J + 1),
        a j * a j' * primeBilinear M (classPole p j M) (classPole p j' M) := by
    rw [atomicWeilForm_eq_primeBilinear, primeBilinear_sum_left]
    refine sum_congr rfl fun j _ => ?_
    rw [primeBilinear_comm, primeBilinear_sum_left, mul_sum]
    refine sum_congr rfl fun j' _ => ?_
    rw [primeBilinear_comm]; ring
  have hQ : qf (classHodgeGram p J M c) a =
      ∑ j : Fin (J + 1), ∑ j' : Fin (J + 1),
        a j * a j' * primeBilinear M (classPole p j M) (classPole p j' M) -
      c * ∑ j : Fin (J + 1), a j ^ 2 * classMass p j M := by
    simp only [qf, bil, dotProduct, mulVec, classHodgeGram]
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun j _ => ?_
    have h : ∀ j' : Fin (J + 1), (primeBilinear M (classPole p j M) (classPole p j' M) -
        c * (if j = j' then classMass p j M else 0)) * a j' =
        primeBilinear M (classPole p j M) (classPole p j' M) * a j' -
          (if j = j' then c * classMass p j M * a j else 0) := by
      intro j'
      by_cases h : j = j'
      · rw [if_pos h, if_pos h]; subst h; ring
      · simp only [if_neg h]; ring
    rw [sum_congr rfl fun j' _ => h j', sum_sub_distrib, sum_ite_eq, if_pos (mem_univ _),
      mul_sub, mul_sum]
    congr 1
    · exact sum_congr rfl fun j' _ => by ring
    · ring
  rw [hP, hQ, sum_classCombination_sq (p := p) a M]

/-- **Hodge index of the matched prime place on the classes.** For `0 < η ≤ min(1/2, log p/4)`,
eventually in `M` the form `P_M − (log M − γ − η)|·|²` on the class pole vectors of depth `≤ J` has
at most one positive square. -/
theorem eventually_isHyperbolic_classHodgeGram (hp : p.Prime) (J : ℕ) {η : ℝ} (hη : 0 < η)
    (hη1 : η ≤ 1 / 2) (hηp : η ≤ Real.log p / 4) :
    ∃ M₀ : ℕ, ∀ M, M₀ ≤ M →
      IsHyperbolic (classHodgeGram p J M (Real.log M - γ - η)) := by
  obtain ⟨M₀, hM₀⟩ := eventually_atomicWeilForm_classCombination_gap_le hp J hη
  refine ⟨M₀, fun M hM => ?_⟩
  set ℓ : (Fin (J + 1) → ℝ) →ₗ[ℝ] ℝ := dotLeft (fun j => classMass p j M)
  refine isHyperbolic_of_nonpos_on_ker (classHodgeGram_isSymm M _) ℓ fun a ha => ?_
  have hL : polarFunctional M (fun n => ∑ j : Fin (J + 1), a j * classPole p j M n) = 0 := by
    rw [polarFunctional_classCombination]
    simpa [ℓ, dotLeft, dotProduct, mul_comm] using ha
  have h := hM₀ M hM a
  rw [hL] at h
  rw [qf_classHodgeGram]
  have hg := one_le_towerMass (p := p) (J := J)
  set X := ∑ n ∈ Icc 1 M, (∑ j : Fin (J + 1), a j * classPole p j M n) ^ 2
  have hX : 0 ≤ X := sum_nonneg fun _ _ => sq_nonneg _
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hgap : 2 * η ≤ (towerMass p J - η) * Real.log p := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hgap hX]

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
