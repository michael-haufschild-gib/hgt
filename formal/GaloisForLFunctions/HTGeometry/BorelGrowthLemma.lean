import Mathlib

/-!
# The Borel growth lemma

The **Borel growth lemma** controls the exceptional set of the Nevanlinna second main theorem:
for a continuous nondecreasing function `T ≥ 1`, the set of radii `r ≥ a` at which
`T(r + 1/T(r)) ≥ 2 T(r)` has Lebesgue measure at most `2`.

The proof is a dyadic band decomposition.  A bad radius with `T(r) ∈ [2^k, 2^{k+1})` satisfies
`T(r + 1/T(r)) ≥ 2 T(r) ≥ 2^{k+1}`, so `r + 1/T(r)` reaches the level `2^{k+1}`; hence `r` lies
within `1/T(r) ≤ 2^{-k}` of the first crossing `s_k` of that level, and below it.  Each band
therefore sits in an interval of length `2^{-k}`, and `∑_{k} 2^{-k} = 2`.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace GaloisForLFunctions.Nevanlinna

/-- Every real `x ≥ 1` lies in a unique dyadic band `[2^k, 2^{k+1})`. -/
theorem exists_dyadic_band {x : ℝ} (hx : 1 ≤ x) :
    ∃ k : ℕ, (2 : ℝ) ^ k ≤ x ∧ x < (2 : ℝ) ^ (k + 1) := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt x (by norm_num : (1 : ℝ) < 2)
  have hex : ∃ k : ℕ, x < (2 : ℝ) ^ (k + 1) := ⟨n, lt_of_lt_of_le hn
    (pow_le_pow_right₀ (by norm_num) (Nat.le_succ n))⟩
  classical
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0]; simpa using hx
  · have hnot := Nat.find_min hex (Nat.pred_lt hpos.ne')
    have hp1 : (Nat.find hex).pred + 1 = Nat.find hex := by
      rw [Nat.pred_eq_sub_one]; omega
    rw [hp1] at hnot
    exact not_lt.mp hnot

/-- **Borel growth lemma.**  If `T` is continuous, nondecreasing and `≥ 1`, the exceptional set
`{ r ≥ a | 2 T(r) ≤ T(r + 1/T(r)) }` — the radii at which the Nevanlinna characteristic doubles
over a step of size `1/T(r)` — has Lebesgue measure at most `2`. -/
theorem borel_growth {T : ℝ → ℝ} (hcont : Continuous T) (hmono : Monotone T)
    (hT1 : ∀ r, 1 ≤ T r) (a : ℝ) :
    volume {r : ℝ | a ≤ r ∧ 2 * T r ≤ T (r + (T r)⁻¹)} ≤ 2 := by
  classical
  set E : Set ℝ := {r : ℝ | a ≤ r ∧ 2 * T r ≤ T (r + (T r)⁻¹)} with hE
  set lvl : ℕ → Set ℝ := fun k => {r : ℝ | a ≤ r ∧ (2 : ℝ) ^ (k + 1) ≤ T r} with hlvl
  set s : ℕ → ℝ := fun k => sInf (lvl k) with hs
  set Ek : ℕ → Set ℝ := fun k => E ∩ {r : ℝ | (2 : ℝ) ^ k ≤ T r ∧ T r < (2 : ℝ) ^ (k + 1)} with hEk
  have hcover : E ⊆ ⋃ k, Ek k := by
    intro r hr
    obtain ⟨k, hk1, hk2⟩ := exists_dyadic_band (hT1 r)
    exact mem_iUnion.mpr ⟨k, hr, hk1, hk2⟩
  have hbandsub : ∀ k, Ek k ⊆ Ico (s k - (2 : ℝ)⁻¹ ^ k) (s k) := by
    intro k r hr
    obtain ⟨⟨har, hEr⟩, hlow, hupp⟩ := hr
    have hTrpos : 0 < T r := lt_of_lt_of_le one_pos (hT1 r)
    have hmem : (r + (T r)⁻¹) ∈ lvl k := by
      refine ⟨by linarith [inv_pos.mpr hTrpos], ?_⟩
      calc (2 : ℝ) ^ (k + 1) = 2 * (2 : ℝ) ^ k := by ring
        _ ≤ 2 * T r := by linarith [hlow]
        _ ≤ T (r + (T r)⁻¹) := hEr
    have hne : (lvl k).Nonempty := ⟨_, hmem⟩
    have hbdd : BddBelow (lvl k) := ⟨a, fun y hy => hy.1⟩
    have hsk_le : s k ≤ r + (T r)⁻¹ := csInf_le hbdd hmem
    have hinv : (T r)⁻¹ ≤ (2 : ℝ)⁻¹ ^ k := by
      rw [inv_pow]; exact inv_anti₀ (by positivity) hlow
    have hlow2 : s k - (2 : ℝ)⁻¹ ^ k ≤ r := by linarith [hsk_le, hinv]
    have hclosed : IsClosed (lvl k) := by
      have heq : lvl k = Ici a ∩ (T ⁻¹' (Ici ((2 : ℝ) ^ (k + 1)))) := by
        ext y; simp [hlvl, mem_Ici, mem_preimage]
      rw [heq]
      exact isClosed_Ici.inter (isClosed_Ici.preimage hcont)
    have hsk_mem : s k ∈ lvl k := hclosed.csInf_mem hne hbdd
    have hupp2 : r < s k := by
      by_contra hcon
      exact absurd (le_trans hsk_mem.2 (hmono (not_lt.mp hcon))) (not_le.mpr hupp)
    exact ⟨hlow2, hupp2⟩
  have hmeas : volume E ≤ ∑' k, volume (Ek k) :=
    le_trans (measure_mono hcover) (measure_iUnion_le _)
  have hband_meas : ∀ k, volume (Ek k) ≤ ENNReal.ofReal ((2 : ℝ)⁻¹ ^ k) := by
    intro k
    refine le_trans (measure_mono (hbandsub k)) (le_of_eq ?_)
    rw [Real.volume_Ico]; congr 1; ring
  calc volume E ≤ ∑' k, volume (Ek k) := hmeas
    _ ≤ ∑' k, ENNReal.ofReal ((2 : ℝ)⁻¹ ^ k) := ENNReal.tsum_le_tsum hband_meas
    _ = ∑' k, ((2 : ℝ≥0∞)⁻¹) ^ k := by
        congr 1; funext k
        rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_inv_of_pos (by norm_num)]
        norm_num
    _ = (1 - (2 : ℝ≥0∞)⁻¹)⁻¹ := ENNReal.tsum_geometric _
    _ = 2 := by
        have hhalf : (2 : ℝ≥0∞)⁻¹ + 2⁻¹ = 1 := by rw [← one_div]; exact ENNReal.add_halves 1
        rw [show (1 : ℝ≥0∞) - 2⁻¹ = 2⁻¹ from ENNReal.sub_eq_of_eq_add (by simp) hhalf.symm, inv_inv]

/-- **Good radii are unbounded.**  A set of Lebesgue measure at most `2` cannot contain a ray, so
beyond every bound there is a radius at which `T` does not double over a step of size `1/T`.  This is
the form in which the growth lemma is used: it supplies the Wiman--Valiron radii, and the exceptional
set never has to be described. -/
theorem exists_ge_lt_two_mul {T : ℝ → ℝ} (hcont : Continuous T) (hmono : Monotone T)
    (hT1 : ∀ r, 1 ≤ T r) (R : ℝ) :
    ∃ r, R ≤ r ∧ T (r + (T r)⁻¹) < 2 * T r := by
  by_contra hcon
  have hbad : ∀ r, R ≤ r → 2 * T r ≤ T (r + (T r)⁻¹) := by
    intro r hr
    by_contra h
    exact hcon ⟨r, hr, not_le.mp h⟩
  have hsub : Ici R ⊆ {r : ℝ | R ≤ r ∧ 2 * T r ≤ T (r + (T r)⁻¹)} :=
    fun r hr => ⟨hr, hbad r hr⟩
  have hvol := le_trans (measure_mono hsub) (borel_growth hcont hmono hT1 R)
  rw [Real.volume_Ici] at hvol
  exact absurd hvol (by simp)

/-- **Good radii in multiplicative form.**  Running the previous corollary in the logarithmic
variable advances the radius by the factor `1 + 1/T(r)` instead of the additive step `1/T(r)`. -/
theorem exists_ge_lt_two_mul_scaled {T : ℝ → ℝ} (hcont : Continuous T) (hmono : Monotone T)
    (hT1 : ∀ r, 1 ≤ T r) {R : ℝ} (hR : 0 < R) :
    ∃ r, R ≤ r ∧ T (r * (1 + (T r)⁻¹)) < 2 * T r := by
  have hSmono : Monotone fun x : ℝ => T (Real.exp x) := fun x y hxy =>
    hmono (Real.exp_le_exp.mpr hxy)
  have hScont : Continuous fun x : ℝ => T (Real.exp x) := hcont.comp Real.continuous_exp
  obtain ⟨x, hx, hxT⟩ :=
    exists_ge_lt_two_mul hScont hSmono (fun x => hT1 (Real.exp x)) (Real.log R)
  refine ⟨Real.exp x, ?_, ?_⟩
  · calc R = Real.exp (Real.log R) := (Real.exp_log hR).symm
      _ ≤ Real.exp x := Real.exp_le_exp.mpr hx
  · have hTr : (0 : ℝ) < T (Real.exp x) := lt_of_lt_of_le one_pos (hT1 _)
    have hrpos : (0 : ℝ) < Real.exp x := Real.exp_pos x
    have hstep : Real.exp x * (1 + (T (Real.exp x))⁻¹)
        ≤ Real.exp (x + (T (Real.exp x))⁻¹) := by
      rw [Real.exp_add]
      refine mul_le_mul_of_nonneg_left ?_ hrpos.le
      have := Real.add_one_le_exp ((T (Real.exp x))⁻¹)
      linarith
    exact lt_of_le_of_lt (hmono hstep) hxT

end GaloisForLFunctions.Nevanlinna
