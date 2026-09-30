import GaloisForLFunctions.RHTower.ZetaNotchTwistedOffDiagonal

/-!
# Detuning shells of the pair weight

For a twist `h/k` and an off-diagonal pair `P`, let `Δ_P = |pairFreq P − log(h/k)|` be its detuning.
The pair weight damped by `(LΔ_P)^{−K}`, summed over the pairs with `Δ_P ≥ δ`, satisfies
(`tsum_farWeight_le`)

`Σ_{Δ_P ≥ δ} pairWeight(P) (LΔ_P)^{−K} ≤ 64 δ k L √(2k/h) (Lδ)^{−K} + ζ₂(5/4) L^{3/4} (L/8)^{−K}`

for `0 < δ ≤ 1/8` and `K ≥ 2`. The pairs with `Δ_P < 1/8` split into dyadic shells
`2^j δ ≤ Δ_P < 2^{j+1} δ`, each contained in the near-resonance at scale `2^{j+1} δ ≤ 1/4`, whose mass
decays like `√(k/h)` (`tsum_nearRes_le'`); the damping `(L 2^j δ)^{−K}` sums geometrically. Unlike
the uniform bound `(Lδ)^{−K} Σ pairWeight`, this decays in the twist height `h`.
-/

noncomputable section

namespace RHTower.ZetaNotch

open Complex MeasureTheory Set Filter Topology RHTower GaloisForLFunctions.HTGeometry

/-- The detuning `|pairFreq P − log(h/k)|` of a pair from the twist `h/k`. -/
def detuning (h k : ℕ) (P : ℕ × ℕ) : ℝ := |pairFreq P - (Real.log h - Real.log k)|

theorem detuning_nonneg (h k : ℕ) (P : ℕ × ℕ) : 0 ≤ detuning h k P := abs_nonneg _

/-- The far weight: `pairWeight(P) (LΔ_P)^{−K}` on the `δ`-detuned off-diagonal pairs. -/
def farWeight (L δ : ℝ) (K : ℕ) (h k : ℕ) (P : ℕ × ℕ) : ℝ :=
  if (P.2 + 1) * k ≠ (P.1 + 1) * h ∧ δ ≤ detuning h k P then
    pairWeight L P * ((L * detuning h k P) ^ K)⁻¹ else 0

theorem farWeight_nonneg {L δ : ℝ} (hL : 0 ≤ L) (K : ℕ) (h k : ℕ) (P : ℕ × ℕ) :
    0 ≤ farWeight L δ K h k P := by
  unfold farWeight
  split_ifs
  · exact mul_nonneg (pairWeight_nonneg hL P)
      (inv_nonneg.mpr (pow_nonneg (mul_nonneg hL (detuning_nonneg h k P)) K))
  · exact le_refl _

theorem nearRes_iff_detuning {h k : ℕ} (hh : 1 ≤ h) (hk : 1 ≤ k) (δ : ℝ) (P : ℕ × ℕ) :
    nearRes h k δ P ↔ (P.2 + 1) * k ≠ (P.1 + 1) * h ∧ detuning h k P < δ := by
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  unfold nearRes detuning pairFreq
  rw [Real.log_div (by positivity) (by positivity), Real.log_div hh0.ne' hk0.ne']

/-- The number of dyadic shells below `1/8`: the least `J` with `1/8 ≤ 2^J δ`. -/
theorem exists_shell_count {δ : ℝ} (hδ : 0 < δ) : ∃ J : ℕ, 1 / 8 ≤ 2 ^ J * δ := by
  obtain ⟨J, hJ⟩ := pow_unbounded_of_one_lt (1 / 8 / δ) (by norm_num : (1 : ℝ) < 2)
  exact ⟨J, by rw [div_lt_iff₀ hδ] at hJ; linarith⟩

/-- A pair with `δ ≤ Δ < 1/8` lies in a dyadic shell `2^j δ ≤ Δ < 2^{j+1} δ` with `2^j δ < 1/8`. -/
theorem exists_shell {δ Δ : ℝ} (hδ : 0 < δ) (hδΔ : δ ≤ Δ) :
    ∃ j : ℕ, 2 ^ j * δ ≤ Δ ∧ Δ < 2 ^ (j + 1) * δ := by
  classical
  have hex : ∃ j : ℕ, Δ < 2 ^ (j + 1) * δ := by
    obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (Δ / δ) (by norm_num : (1 : ℝ) < 2)
    refine ⟨j, ?_⟩
    rw [div_lt_iff₀ hδ] at hj
    have : (2 : ℝ) ^ j ≤ 2 ^ (j + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    nlinarith
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0, pow_zero, one_mul]; exact hδΔ
  · have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    push Not at this
    rwa [show Nat.find hex - 1 + 1 = Nat.find hex by omega] at this

/-- The shell term at scale `j`. -/
def shellWeight (L δ : ℝ) (K : ℕ) (h k : ℕ) (j : ℕ) (P : ℕ × ℕ) : ℝ :=
  if nearRes h k (2 ^ (j + 1) * δ) P then pairWeight L P * ((L * (2 ^ j * δ)) ^ K)⁻¹ else 0

theorem shellWeight_nonneg {L δ : ℝ} (hL : 0 ≤ L) (hδ : 0 ≤ δ) (K : ℕ) (h k j : ℕ) (P : ℕ × ℕ) :
    0 ≤ shellWeight L δ K h k j P := by
  unfold shellWeight
  split_ifs
  · exact mul_nonneg (pairWeight_nonneg hL P) (inv_nonneg.mpr (by positivity))
  · exact le_refl _

/-- **Pointwise shell bound.** -/
theorem farWeight_le_shells {h k : ℕ} (hh : 1 ≤ h) (hk : 1 ≤ k) {L δ : ℝ} (hL : 0 < L)
    (hδ : 0 < δ) (K : ℕ) {J : ℕ} (hJ : 1 / 8 ≤ 2 ^ J * δ) (P : ℕ × ℕ) :
    farWeight L δ K h k P ≤ ∑ j ∈ Finset.range J, shellWeight L δ K h k j P +
      pairWeight L P * ((L / 8) ^ K)⁻¹ := by
  have hw0 := pairWeight_nonneg hL.le P
  have hsh0 : 0 ≤ ∑ j ∈ Finset.range J, shellWeight L δ K h k j P :=
    Finset.sum_nonneg fun j _ => shellWeight_nonneg hL.le hδ.le K h k j P
  unfold farWeight
  split_ifs with hfar
  swap
  · have : 0 ≤ pairWeight L P * ((L / 8) ^ K)⁻¹ := mul_nonneg hw0 (by positivity)
    linarith
  obtain ⟨hne, hδΔ⟩ := hfar
  set Δ := detuning h k P with hΔ
  rcases le_or_gt (1 / 8) Δ with hbig | hsmall
  · have h1 : ((L * Δ) ^ K)⁻¹ ≤ ((L / 8) ^ K)⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) (by nlinarith) K)
    have := mul_le_mul_of_nonneg_left h1 hw0
    linarith
  · obtain ⟨j, hj1, hj2⟩ := exists_shell hδ hδΔ
    have hjJ : j < J := by
      by_contra hc
      push Not at hc
      have : (2 : ℝ) ^ J ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hc
      nlinarith
    have hnear : nearRes h k (2 ^ (j + 1) * δ) P :=
      (nearRes_iff_detuning hh hk _ P).mpr ⟨hne, hj2⟩
    have hterm : pairWeight L P * ((L * Δ) ^ K)⁻¹ ≤ shellWeight L δ K h k j P := by
      unfold shellWeight
      rw [if_pos hnear]
      refine mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity)
        (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hj1 hL.le) K)) hw0
    have hsum : shellWeight L δ K h k j P ≤ ∑ j ∈ Finset.range J, shellWeight L δ K h k j P :=
      Finset.single_le_sum (fun i _ => shellWeight_nonneg hL.le hδ.le K h k i P)
        (Finset.mem_range.mpr hjJ)
    have : 0 ≤ pairWeight L P * ((L / 8) ^ K)⁻¹ := mul_nonneg hw0 (by positivity)
    linarith

theorem summable_shellWeight {h k : ℕ} {L δ : ℝ} (hL : 0 < L) (hδ : 0 ≤ δ) (K j : ℕ) :
    Summable (shellWeight L δ K h k j) := by
  refine Summable.of_nonneg_of_le (shellWeight_nonneg hL.le hδ K h k j) (fun P => ?_)
    ((summable_pairWeight hL.le).mul_right (((L * (2 ^ j * δ)) ^ K)⁻¹))
  unfold shellWeight
  split_ifs
  · exact le_refl _
  · exact mul_nonneg (pairWeight_nonneg hL.le P) (inv_nonneg.mpr (by positivity))

/-- The mass of one shell: `≤ 16·2^{j+1} δ k L √(2k/h) (L 2^j δ)^{−K}`. -/
theorem tsum_shellWeight_le {h k : ℕ} (hh : 1 ≤ h) (hk : 1 ≤ k) {L δ : ℝ} (hL : 0 < L)
    (hδ : 0 < δ) (K j : ℕ) (hj : 2 ^ (j + 1) * δ ≤ 1 / 4) :
    ∑' P, shellWeight L δ K h k j P ≤
      16 * (2 ^ (j + 1) * δ) * k * L * Real.sqrt (2 * k / h) * ((L * (2 ^ j * δ)) ^ K)⁻¹ := by
  have e : (fun P => shellWeight L δ K h k j P) = fun P =>
      (if nearRes h k (2 ^ (j + 1) * δ) P then pairWeight L P else 0) *
        ((L * (2 ^ j * δ)) ^ K)⁻¹ := by
    funext P
    unfold shellWeight
    split_ifs <;> simp
  rw [e, tsum_mul_right]
  exact mul_le_mul_of_nonneg_right (tsum_nearRes_le' hh hk (by positivity) hj hL)
    (inv_nonneg.mpr (by positivity))

theorem shell_factor_le {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) {K : ℕ} (hK : 2 ≤ K) (j : ℕ) :
    16 * (2 ^ (j + 1) * δ) * ((L * (2 ^ j * δ)) ^ K)⁻¹ ≤ 32 * δ * ((L * δ) ^ K)⁻¹ * (1 / 2) ^ j := by
  have hpos : 0 < (L * δ) ^ K := by positivity
  have h2 : (0 : ℝ) < 2 ^ j := by positivity
  have e : (L * (2 ^ j * δ)) ^ K = (2 ^ j) ^ K * (L * δ) ^ K := by ring
  rw [e, mul_inv, pow_succ]
  have hK' : (2 : ℝ) ^ j * 2 ^ j ≤ (2 ^ j) ^ K := by
    rw [← sq]; exact pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) hK
  have hinv : (((2 : ℝ) ^ j) ^ K)⁻¹ ≤ (2 ^ j * 2 ^ j)⁻¹ := inv_anti₀ (by positivity) hK'
  have hhalf : ((1 : ℝ) / 2) ^ j = (2 ^ j)⁻¹ := by rw [one_div, inv_pow]
  rw [hhalf]
  calc 16 * (2 ^ j * 2 * δ) * ((((2 : ℝ) ^ j) ^ K)⁻¹ * ((L * δ) ^ K)⁻¹)
      ≤ 16 * (2 ^ j * 2 * δ) * ((2 ^ j * 2 ^ j)⁻¹ * ((L * δ) ^ K)⁻¹) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hinv (by positivity)) (by positivity)
    _ = 32 * δ * ((L * δ) ^ K)⁻¹ * (2 ^ j)⁻¹ := by field_simp; norm_num

/-- **Detuning-shell bound for the far weight.** -/
theorem tsum_farWeight_le {h k : ℕ} (hh : 1 ≤ h) (hk : 1 ≤ k) {L δ : ℝ} (hL : 0 < L)
    (hδ : 0 < δ) {K : ℕ} (hK : 2 ≤ K) :
    Summable (farWeight L δ K h k) ∧
      ∑' P, farWeight L δ K h k P ≤
        64 * δ * k * L * Real.sqrt (2 * k / h) * ((L * δ) ^ K)⁻¹ +
          pairZeta * L ^ (3 / 4 : ℝ) * ((L / 8) ^ K)⁻¹ := by
  classical
  have hex := exists_shell_count hδ
  set J := Nat.find hex with hJdef
  have hJ : 1 / 8 ≤ 2 ^ J * δ := Nat.find_spec hex
  have hpt := farWeight_le_shells hh hk hL hδ K hJ
  have hsumsh : ∀ j ∈ Finset.range J, Summable (shellWeight L δ K h k j) :=
    fun j _ => summable_shellWeight hL hδ.le K j
  have hmaj : Summable fun P => ∑ j ∈ Finset.range J, shellWeight L δ K h k j P +
      pairWeight L P * ((L / 8) ^ K)⁻¹ :=
    (summable_sum hsumsh).add ((summable_pairWeight hL.le).mul_right _)
  have hfs : Summable (farWeight L δ K h k) :=
    Summable.of_nonneg_of_le (farWeight_nonneg hL.le K h k) hpt hmaj
  refine ⟨hfs, ?_⟩
  set c : ℝ := 32 * δ * k * L * Real.sqrt (2 * k / h) * ((L * δ) ^ K)⁻¹ with hc
  have hshell : ∀ j ∈ Finset.range J, ∑' P, shellWeight L δ K h k j P ≤ c * (1 / 2) ^ j := by
    intro j hj
    have hjJ : j < J := Finset.mem_range.mp hj
    have hjs : ¬ (1 / 8 ≤ 2 ^ j * δ) := Nat.find_min hex hjJ
    push Not at hjs
    have hj4 : 2 ^ (j + 1) * δ ≤ 1 / 4 := by rw [pow_succ]; linarith
    refine (tsum_shellWeight_le hh hk hL hδ K j hj4).trans ?_
    have hf := shell_factor_le hL hδ hK j
    have hk0 : (0 : ℝ) ≤ k * L * Real.sqrt (2 * k / h) := by positivity
    calc 16 * (2 ^ (j + 1) * δ) * k * L * Real.sqrt (2 * k / h) * ((L * (2 ^ j * δ)) ^ K)⁻¹
        = (16 * (2 ^ (j + 1) * δ) * ((L * (2 ^ j * δ)) ^ K)⁻¹) * (k * L * Real.sqrt (2 * k / h)) := by
          ring
      _ ≤ (32 * δ * ((L * δ) ^ K)⁻¹ * (1 / 2) ^ j) * (k * L * Real.sqrt (2 * k / h)) :=
          mul_le_mul_of_nonneg_right hf hk0
      _ = c * (1 / 2) ^ j := by rw [hc]; ring
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  calc ∑' P, farWeight L δ K h k P
      ≤ ∑' P, (∑ j ∈ Finset.range J, shellWeight L δ K h k j P +
          pairWeight L P * ((L / 8) ^ K)⁻¹) := hfs.tsum_le_tsum hpt hmaj
    _ = ∑ j ∈ Finset.range J, ∑' P, shellWeight L δ K h k j P +
          (∑' P, pairWeight L P) * ((L / 8) ^ K)⁻¹ := by
        rw [Summable.tsum_add (summable_sum hsumsh) ((summable_pairWeight hL.le).mul_right _),
          Summable.tsum_finsetSum hsumsh, tsum_mul_right]
    _ ≤ ∑ j ∈ Finset.range J, c * (1 / 2) ^ j +
          pairZeta * L ^ (3 / 4 : ℝ) * ((L / 8) ^ K)⁻¹ := by
        gcongr with j hj
        · exact hshell j hj
        · exact tsum_pairWeight_le hL.le
    _ ≤ c * 2 + pairZeta * L ^ (3 / 4 : ℝ) * ((L / 8) ^ K)⁻¹ := by
        rw [← Finset.mul_sum]
        gcongr
        exact sum_geometric_two_le J
    _ = 64 * δ * k * L * Real.sqrt (2 * k / h) * ((L * δ) ^ K)⁻¹ +
          pairZeta * L ^ (3 / 4 : ℝ) * ((L / 8) ^ K)⁻¹ := by rw [hc]; ring

end RHTower.ZetaNotch
