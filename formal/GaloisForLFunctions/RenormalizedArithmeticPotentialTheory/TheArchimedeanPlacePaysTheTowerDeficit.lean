import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheSignOfTheTowerFinitePart
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheFinitePartIsEulersConstant
import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheMetzlerDichotomy

/-!
# The archimedean place pays the tower deficit

The horizon renormalization subtracts from the prime form, on the `p`-adic class `j`, its own
divergence `log(M/p^j) + γ_p` per unit mass, and leaves the tower finite part
`F_p = 2γ_p + log p (1 − K_{p^{−1/2}})`, which is negative by `2 d_p` at the small primes
(`TheSignOfTheTowerFinitePart`). The archimedean place does not see classes: the self-energy of an
atom of width `w` is `log(1/w)` on every atom. Matched against it, the prime form keeps the
**valuation potential** `j log p` on the class `j`, and this potential pays the deficit exactly.

* **The valuation Gram is in the stability regime** (`valuationGram`,
  `valuationGram_mulVec_one_nonpos`, `sum_cross_le_valuation`): for any masses with
  `m_{j+1} ≤ m_j/p`, the Metzler matrix with diagonal `−m_j (j + 1/(p − 1))` and off-diagonal
  `m_{max(j, j')}` has nonpositive row sums, so (Metzler dichotomy, ALG)
  `Σ_{j ≠ j'} a_j a_{j'} m_{max(j, j')} ≤ Σ_j a_j² m_j (j + 1/(p − 1))`.
* **Class masses descend by the degree** (`classMass_succ_le`): `|w_{j+1}|² ≤ |w_j|²/p`, exactly, at
  every horizon `M`.
* **The deficit is paid** (`towerFinitePart_add_valuation_ge`): in normalized class coordinates
  `F_p(b) + Σ_j j log p · b_j² ≥ (γ + γ_p) |b|²`. Without the potential the sharp bound is
  `−2d_p |b|²`; with it the form is positive with margin `γ + γ_p`, for every prime.
* **The matched prime form on the classes** (`eventually_atomicWeilForm_classCombination_le`): for every
  `η > 0`, eventually in `M`, every combination `x = Σ_{j ≤ J} a_j w_j^{(M)}` of class pole vectors
  satisfies `P_M(x) ≤ (log M − γ + η) |x|²`.
* **Sharpness** (`eventually_atomicWeilForm_truncPole_ge`): the pole vector, the sum of all class
  pole vectors, has `P_M(u) ≥ (log M − γ − η)|u|²`.

So on every `p`-adic class profile the prime form exceeds the archimedean counterterm `log M` by
at most `−γ`, the finite part of the pole vector: the pole is the extremal class profile, and no
small prime leaves a deficit for the archimedean place. Equivalently `log M − P_M + γ ≥ 0` on the
classes, with the pole as its ground state; in normalized coordinates this is the operator
`diag(j log p) + γ_p + log p − log p K_{p^{−1/2}}`, whose exact eigenvector `p^{−j/2}` (the pole
profile) has eigenvalue `γ`.
-/

noncomputable section

open Filter Topology Finset Matrix

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open GaloisForLFunctions.ArithmeticIntersectionTheory GaloisForLFunctions.ArithmeticElectrostatics
  GaloisForLFunctions.ArithmeticLorentzianGeometry

local notation "γ" => Real.eulerMascheroniConstant

/-! ### 1. The valuation Gram -/

/-- The **valuation Gram** of masses `m`: diagonal `−m_j (j + 1/(p − 1))`, off-diagonal
`m_{max(j, j')}`. -/
def valuationGram (p J : ℕ) (m : ℕ → ℝ) : Matrix (Fin (J + 1)) (Fin (J + 1)) ℝ :=
  fun j j' => if j = j' then -(m j * ((j : ℝ) + 1 / ((p : ℝ) - 1))) else m (max (j : ℕ) j')

variable {p J : ℕ} {m : ℕ → ℝ}

theorem valuationGram_isSymm : (valuationGram p J m).IsSymm := by
  ext j j'
  simp only [Matrix.transpose_apply, valuationGram]
  by_cases h : j = j'
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h), max_comm]

theorem valuationGram_isMetzler (hm : ∀ j, 0 ≤ m j) : IsMetzler (valuationGram p J m) :=
  fun j j' h => by simp only [valuationGram, if_neg h]; exact hm _

/-- Masses descending by the factor `p` have tails at most `m_j/(p − 1)`. -/
theorem sum_range_shift_le (hp : 1 < (p : ℝ)) (hm0 : ∀ j, 0 ≤ m j)
    (hm : ∀ j, m (j + 1) ≤ m j / p) (K : ℕ) :
    ∀ j, ∑ k ∈ range K, m (j + 1 + k) ≤ m j / ((p : ℝ) - 1) := by
  have hp1 : 0 < (p : ℝ) - 1 := by linarith
  induction K with
  | zero => intro j; simp only [range_zero, sum_empty]; exact div_nonneg (hm0 j) hp1.le
  | succ K ih =>
    intro j
    rw [sum_range_succ']
    have h1 := ih (j + 1)
    have h2 := hm j
    simp only [add_zero]
    rw [sum_congr rfl fun k _ => by rw [show j + 1 + (k + 1) = j + 1 + 1 + k by ring]]
    calc ∑ k ∈ range K, m (j + 1 + 1 + k) + m (j + 1)
        ≤ m (j + 1) / ((p : ℝ) - 1) + m (j + 1) := add_le_add h1 le_rfl
      _ = m (j + 1) * p / ((p : ℝ) - 1) := by field_simp; ring
      _ ≤ m j / p * p / ((p : ℝ) - 1) := by gcongr
      _ = m j / ((p : ℝ) - 1) := by field_simp

/-- **The row sums of the valuation Gram are nonpositive.** -/
theorem valuationGram_mulVec_one_nonpos (hp : 1 < (p : ℝ)) (hm0 : ∀ j, 0 ≤ m j)
    (hm : ∀ j, m (j + 1) ≤ m j / p) (j : Fin (J + 1)) :
    (valuationGram p J m *ᵥ fun _ => (1 : ℝ)) j ≤ 0 := by
  have hj : (j : ℕ) ≤ J := Nat.lt_succ_iff.mp j.2
  simp only [mulVec, dotProduct, mul_one, valuationGram]
  set f : ℕ → ℝ := fun i => if i = (j : ℕ) then -(m j * ((j : ℝ) + 1 / ((p : ℝ) - 1)))
    else m (max (j : ℕ) i) with hf
  have hrw : ∑ x : Fin (J + 1), (if j = x then -(m j * ((j : ℝ) + 1 / ((p : ℝ) - 1)))
      else m (max (j : ℕ) x)) = ∑ i ∈ range (J + 1), f i := by
    rw [← Fin.sum_univ_eq_sum_range f]
    refine sum_congr rfl fun x _ => ?_
    simp only [hf]
    by_cases h : j = x
    · subst h; simp
    · rw [if_neg h, if_neg (fun h' => h (Fin.ext h'.symm))]
  rw [hrw, ← sum_range_add_sum_Ico f (by omega : (j : ℕ) ≤ J + 1),
    sum_eq_sum_Ico_succ_bot (by omega : (j : ℕ) < J + 1), sum_Ico_eq_sum_range]
  have hlow : ∑ i ∈ range (j : ℕ), f i = (j : ℝ) * m j := by
    have h : ∀ i ∈ range (j : ℕ), f i = m j := fun i hi => by
      have hi' : i < (j : ℕ) := mem_range.mp hi
      simp only [hf, if_neg hi'.ne, max_eq_left hi'.le]
    rw [sum_congr rfl h, sum_const, card_range, nsmul_eq_mul]
  have hhigh : ∑ k ∈ range (J + 1 - ((j : ℕ) + 1)), f ((j : ℕ) + 1 + k) =
      ∑ k ∈ range (J + 1 - ((j : ℕ) + 1)), m ((j : ℕ) + 1 + k) :=
    sum_congr rfl fun k _ => by
      simp only [hf, if_neg (by omega : (j : ℕ) + 1 + k ≠ j), max_eq_right (by omega :
        (j : ℕ) ≤ (j : ℕ) + 1 + k)]
  have htail := sum_range_shift_le hp hm0 hm (J + 1 - ((j : ℕ) + 1)) j
  rw [hlow, hhigh]
  simp only [hf, if_pos rfl]
  have : m j * ((j : ℝ) + 1 / ((p : ℝ) - 1)) = (j : ℝ) * m j + m j / ((p : ℝ) - 1) := by ring
  linarith

/-- **The valuation inequality**: for masses with `m_{j+1} ≤ m_j/p`,
`Σ_{j ≠ j'} a_j a_{j'} m_{max(j, j')} ≤ Σ_j a_j² m_j (j + 1/(p − 1))`. The valuation Gram is Metzler
with nonpositive row sums against the constant weight, hence negative semidefinite. -/
theorem sum_cross_le_valuation (hp : 1 < (p : ℝ)) (hm0 : ∀ j, 0 ≤ m j)
    (hm : ∀ j, m (j + 1) ≤ m j / p) (a : Fin (J + 1) → ℝ) :
    ∑ j : Fin (J + 1), ∑ j' : Fin (J + 1),
        (if j = j' then 0 else a j * a j' * m (max (j : ℕ) j')) ≤
      ∑ j : Fin (J + 1), a j ^ 2 * (m j * ((j : ℝ) + 1 / ((p : ℝ) - 1))) := by
  have hq := qf_nonpos_of_mulVec_nonpos (valuationGram_isSymm (p := p) (J := J) (m := m))
    (valuationGram_isMetzler hm0) (π := fun _ => (1 : ℝ)) (fun _ => one_pos)
    (valuationGram_mulVec_one_nonpos hp hm0 hm) a
  have hrow : ∀ j : Fin (J + 1), ∑ j', valuationGram p J m j j' * a j' =
      ∑ j', (if j = j' then 0 else m (max (j : ℕ) j') * a j') -
        m j * ((j : ℝ) + 1 / ((p : ℝ) - 1)) * a j := by
    intro j
    have h : ∀ j', valuationGram p J m j j' * a j' =
        (if j = j' then 0 else m (max (j : ℕ) j') * a j') +
          (if j = j' then -(m j * ((j : ℝ) + 1 / ((p : ℝ) - 1)) * a j') else 0) := by
      intro j'
      by_cases h : j = j'
      · subst h; simp [valuationGram]
      · simp [valuationGram, h]
    rw [sum_congr rfl fun j' _ => h j', sum_add_distrib, sum_ite_eq, if_pos (mem_univ j)]
    ring
  have hexp : qf (valuationGram p J m) a =
      ∑ j : Fin (J + 1), ∑ j' : Fin (J + 1),
        (if j = j' then 0 else a j * a j' * m (max (j : ℕ) j')) -
      ∑ j : Fin (J + 1), a j ^ 2 * (m j * ((j : ℝ) + 1 / ((p : ℝ) - 1))) := by
    simp only [qf, bil, dotProduct, mulVec]
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun j _ => ?_
    rw [hrow j, mul_sub, mul_sum]
    congr 1
    · refine sum_congr rfl fun j' _ => ?_
      split_ifs <;> ring
    · ring
  linarith

/-! ### 2. Class masses descend by the degree -/

theorem unitHarmonic_mono (p : ℕ) {X Y : ℕ} (h : X ≤ Y) : unitHarmonic p X ≤ unitHarmonic p Y := by
  unfold unitHarmonic
  refine sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ (Icc_subset_Icc le_rfl h))
    fun k _ _ => by positivity

/-- **Class masses descend by the degree**: `|w_{j+1}|² ≤ |w_j|²/p` at every horizon. -/
theorem classMass_succ_le (hp : p.Prime) (j M : ℕ) :
    classMass p (j + 1) M ≤ classMass p j M / p := by
  rw [classMass_eq_unitHarmonic hp, classMass_eq_unitHarmonic hp]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hdiv : M / p ^ (j + 1) ≤ M / p ^ j := Nat.div_le_div_left
    (Nat.pow_le_pow_right hp.pos (Nat.le_succ j)) (pow_pos hp.pos j)
  have hU := unitHarmonic_mono p hdiv
  rw [pow_succ, div_div]
  exact div_le_div_of_nonneg_right hU (by positivity)

/-! ### 3. The deficit is paid in normalized coordinates -/

/-- **The valuation potential pays the tower deficit.** In normalized class coordinates,
`F_p(b) + Σ_j j log p b_j² ≥ (γ + γ_p) |b|²` at every depth. -/
theorem towerFinitePart_add_valuation_ge (hp : p.Prime) (b : ℕ → ℝ) :
    (γ + localEuler p) * ∑ j ∈ range (J + 1), b j ^ 2 ≤
      towerFinitePart p (J + 1) b + ∑ j ∈ range (J + 1), (j : ℝ) * Real.log p * b j ^ 2 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  set r : ℝ := 1 / Real.sqrt p with hr
  have hsq : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp0.le
  have hs0 : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hr0 : 0 < r := by positivity
  -- normalized coordinates: `a_j = b_j / r^j`, masses `m_j = r^{2j} = p^{−j}`
  set m : ℕ → ℝ := fun j => r ^ (2 * j) with hm
  have hm0 : ∀ j, 0 ≤ m j := fun j => by positivity
  have hr2 : r ^ 2 = 1 / p := by rw [hr, div_pow, hsq, one_pow]
  have hmsucc : ∀ j, m (j + 1) ≤ m j / p := fun j => by
    simp only [hm, show 2 * (j + 1) = 2 * j + 2 by ring, pow_add, hr2]
    rw [mul_one_div]
  set a : Fin (J + 1) → ℝ := fun j => b j / r ^ (j : ℕ) with ha
  have hmain := sum_cross_le_valuation (J := J) hp1 hm0 hmsucc a
  -- the two sides in normalized coordinates
  have hdiag : ∀ j : ℕ, (b j / r ^ j) ^ 2 * m j = b j ^ 2 := fun j => by
    have hrj : r ^ j ≠ 0 := pow_ne_zero _ hr0.ne'
    simp only [hm]
    rw [show r ^ (2 * j) = (r ^ j) ^ 2 by rw [← pow_mul, mul_comm], div_pow]
    field_simp
  have hcrossE : ∀ i j : ℕ, i ≠ j → b i / r ^ i * (b j / r ^ j) * m (max i j) =
      b i * b j * kmsEntry r i j := fun i j _ => by
    simp only [hm, kmsEntry]
    rcases le_total i j with h | h
    · rw [max_eq_right h, min_eq_left h]
      have e : r ^ (2 * j) = r ^ i * r ^ j * r ^ (j - i) := by
        rw [← pow_add, ← pow_add]; congr 1; omega
      rw [e]; field_simp
    · rw [max_eq_left h, min_eq_right h]
      have e : r ^ (2 * i) = r ^ i * r ^ j * r ^ (i - j) := by
        rw [← pow_add, ← pow_add]; congr 1; omega
      rw [e]; field_simp
  have hK : kmsForm r (J + 1) b =
      ∑ i : Fin (J + 1), ∑ j : Fin (J + 1), b i * b j * kmsEntry r i j := by
    rw [kmsForm, ← Fin.sum_univ_eq_sum_range
      (fun i => ∑ j ∈ range (J + 1), b i * b j * kmsEntry r i j)]
    exact sum_congr rfl fun i _ =>
      (Fin.sum_univ_eq_sum_range (fun j => b i * b j * kmsEntry r i j) (J + 1)).symm
  have hB : ∑ j ∈ range (J + 1), b j ^ 2 = ∑ j : Fin (J + 1), b j ^ 2 :=
    (Fin.sum_univ_eq_sum_range (fun j => b j ^ 2) (J + 1)).symm
  have hL : ∑ j : Fin (J + 1), ∑ j' : Fin (J + 1),
      (if j = j' then 0 else a j * a j' * m (max (j : ℕ) j')) =
      kmsForm r (J + 1) b - ∑ j ∈ range (J + 1), b j ^ 2 := by
    rw [hK, hB, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ => ?_
    have hterm : ∀ j : Fin (J + 1), (if i = j then 0 else a i * a j * m (max (i : ℕ) j)) =
        b i * b j * kmsEntry r i j - (if i = j then b i ^ 2 else 0) := by
      intro j
      by_cases h : i = j
      · subst h; simp [kmsEntry]; ring
      · rw [if_neg h, if_neg h, sub_zero, ha]
        exact hcrossE i j (fun h' => h (Fin.ext h'))
    rw [sum_congr rfl fun j _ => hterm j, sum_sub_distrib, sum_ite_eq, if_pos (mem_univ _)]
  have hR : ∑ j : Fin (J + 1), a j ^ 2 * (m j * ((j : ℝ) + 1 / ((p : ℝ) - 1))) =
      ∑ j ∈ range (J + 1), b j ^ 2 * ((j : ℝ) + 1 / ((p : ℝ) - 1)) := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => b j ^ 2 * ((j : ℝ) + 1 / ((p : ℝ) - 1)))]
    refine sum_congr rfl fun j _ => ?_
    rw [← mul_assoc, ha, hdiag]
  rw [hL, hR] at hmain
  unfold towerFinitePart localEuler
  have hlogp : 0 < Real.log p := Real.log_pos hp1
  have hexp : ∑ j ∈ range (J + 1), b j ^ 2 * ((j : ℝ) + 1 / ((p : ℝ) - 1)) =
      ∑ j ∈ range (J + 1), (j : ℝ) * b j ^ 2 + 1 / ((p : ℝ) - 1) * ∑ j ∈ range (J + 1), b j ^ 2 := by
    rw [mul_sum, ← sum_add_distrib]; exact sum_congr rfl fun j _ => by ring
  have hpot : ∑ j ∈ range (J + 1), (j : ℝ) * Real.log p * b j ^ 2 =
      Real.log p * ∑ j ∈ range (J + 1), (j : ℝ) * b j ^ 2 := by
    rw [mul_sum]; exact sum_congr rfl fun j _ => by ring
  rw [hexp] at hmain
  rw [hpot, show 1 / Real.sqrt p = r from rfl]
  have hk := mul_le_mul_of_nonneg_left hmain hlogp.le
  have e : Real.log p / ((p : ℝ) - 1) = Real.log p * (1 / ((p : ℝ) - 1)) := by ring
  rw [e]
  nlinarith [hk]

/-! ### 4. The matched prime form on the classes -/

/-- **The matched prime form on the `p`-adic classes.** For every depth `J` and `η > 0`, eventually in
`M`, every class combination `x = Σ_{j ≤ J} a_j w_j^{(M)}` satisfies `P_M(x) ≤ (log M − γ + η)|x|²`. -/
theorem eventually_atomicWeilForm_classCombination_le (hp : p.Prime) (J : ℕ) {η : ℝ}
    (hη : 0 < η) :
    ∃ M₀ : ℕ, ∀ M, M₀ ≤ M → ∀ a : Fin (J + 1) → ℝ,
      atomicWeilForm M (fun n => ∑ j : Fin (J + 1), a j * classPole p j M n) ≤
        (Real.log M - γ + η) *
          ∑ n ∈ Icc 1 M, (∑ j : Fin (J + 1), a j * classPole p j M n) ^ 2 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hlogp : 0 < Real.log p := Real.log_pos hp1
  obtain ⟨C, hC⟩ := exists_abs_atomicWeilForm_classCombination_finitePart_le hp J
    (η := η / 3) (by positivity)
  set C' : ℝ := max C 0
  -- eventually: masses close to their asymptotics and large
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
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp ((eventually_all.mpr hev))
  refine ⟨M₀, fun M hM a => ?_⟩
  have hmass := fun j => hM₀ M hM j
  set mm : ℕ → ℝ := fun j => classMass p j M
  have hmm0 : ∀ j, 0 ≤ mm j := fun j => classMass_nonneg p j M
  have hval := sum_cross_le_valuation (J := J) hp1 hmm0 (fun j => classMass_succ_le hp j M) a
  have hnorm := sum_classCombination_sq (p := p) a M
  have hfin := hC M a
  rw [hnorm]
  -- the class diagonal: `m_j²/δ_j ≤ m_j (log M − j log p + γ_p + η/3)`
  have hdiag : ∀ j : Fin (J + 1), (a j * classMass p j M) ^ 2 / classDensity p j ≤
      a j ^ 2 * classMass p j M * (Real.log M - j * Real.log p + localEuler p + η / 3) := by
    intro j
    have hδ := classDensity_pos hp j
    have hm0 := classMass_nonneg p j M
    rw [div_le_iff₀ hδ]
    have := (hmass j).1
    have e : (a j * classMass p j M) ^ 2 = a j ^ 2 * classMass p j M * classMass p j M := by ring
    rw [e]
    calc a j ^ 2 * classMass p j M * classMass p j M
        ≤ a j ^ 2 * classMass p j M *
            (classDensity p j * (Real.log M - j * Real.log p + localEuler p + η / 3)) :=
          mul_le_mul_of_nonneg_left this (mul_nonneg (sq_nonneg _) hm0)
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
  have hsplit : ∑ j : Fin (J + 1), a j ^ 2 * classMass p j M *
      (Real.log M - j * Real.log p + localEuler p + η / 3) =
      (Real.log M + localEuler p + η / 3) * ∑ j : Fin (J + 1), a j ^ 2 * classMass p j M -
        Real.log p * ∑ j : Fin (J + 1), a j ^ 2 * classMass p j M * j := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib]; exact sum_congr rfl fun j _ => by ring
  have hval' : Real.log p * ∑ j : Fin (J + 1), ∑ j' : Fin (J + 1),
      (if j = j' then 0 else a j * a j' * classMass p (max (j : ℕ) j') M) ≤
      Real.log p * ∑ j : Fin (J + 1), a j ^ 2 * classMass p j M * j +
        Real.log p / ((p : ℝ) - 1) * ∑ j : Fin (J + 1), a j ^ 2 * classMass p j M := by
    have := mul_le_mul_of_nonneg_left hval hlogp.le
    refine this.trans (le_of_eq ?_)
    rw [mul_sum, mul_sum, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun j _ => by simp only [mm]; ring
  have hsum2 : ∑ j : Fin (J + 1), a j ^ 2 * (2 * η / 3 * classMass p j M) =
      2 * η / 3 * ∑ j : Fin (J + 1), a j ^ 2 * classMass p j M := by
    rw [mul_sum]; exact sum_congr rfl fun j _ => by ring
  have hsum1 : ∑ j : Fin (J + 1), a j ^ 2 * (η / 3 * classMass p j M + C) ≤
      2 * η / 3 * ∑ j : Fin (J + 1), a j ^ 2 * classMass p j M := hsum2 ▸ hE
  have habs := (abs_le.mp (hfin.trans hsum1)).2
  unfold localEuler at hsplit hval' habs hD
  linarith [hD, hsplit, hval', habs]

/-! ### 5. Sharpness at the pole -/

/-- **The constant `−γ` is attained by the pole vector**: `P_M(u) ≥ (log M − γ − η)|u|²`
eventually. -/
theorem eventually_atomicWeilForm_truncPole_ge {η : ℝ} (hη : 0 < η) :
    ∃ M₀ : ℕ, ∀ M, M₀ ≤ M →
      (Real.log M - γ - η) * ∑ n ∈ Icc 1 M, truncPole M n ^ 2 ≤
        atomicWeilForm M (truncPole M) := by
  obtain ⟨C, hC⟩ := exists_abs_primeBilinear_truncPole_finitePart_le (η := η / 3) (by positivity)
  have hH := tendsto_harmonicSum_sub_log
  have h1 : ∀ᶠ M : ℕ in atTop, harmonicSum M - Real.log M < γ + η / 3 :=
    hH.eventually (gt_mem_nhds (by linarith))
  have h2 : ∀ᶠ M : ℕ in atTop, γ - η / 3 < harmonicSum M - Real.log M :=
    hH.eventually (lt_mem_nhds (by linarith))
  have hHt : Tendsto (fun M : ℕ => harmonicSum M) atTop atTop := by
    have := hH.add_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    exact this.congr fun M => by simp
  have h3 := hHt.eventually_ge_atTop (3 * |C| / η)
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp (h1.and (h2.and (h3.and (eventually_ge_atTop 1))))
  refine ⟨M₀, fun M hM => ?_⟩
  obtain ⟨hM1, hM2, hM3, hM4⟩ := hM₀ M hM
  have hu : ∑ n ∈ Icc 1 M, truncPole M n ^ 2 = harmonicSum M := by
    unfold harmonicSum
    refine sum_congr rfl fun n hn => ?_
    have hn1 := (mem_Icc.mp hn).1
    have hnM := (mem_Icc.mp hn).2
    simp only [truncPole, if_pos hnM, poleVector]
    rw [div_pow, one_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  rw [hu, atomicWeilForm_eq_primeBilinear]
  have hb := (abs_le.mp (hC M M M hM4 le_rfl le_rfl)).1
  have hH0 : 0 ≤ harmonicSum M := le_trans (by positivity) hM3
  have hCl : |C| ≤ η / 3 * harmonicSum M := by
    rw [div_le_iff₀ hη] at hM3; linarith
  nlinarith [le_abs_self C, neg_abs_le C]

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
