import GaloisForLFunctions.HTGeometry.NevanlinnaEntireCharacteristic
import Mathlib.Analysis.Complex.ValueDistribution.FirstMainTheorem

/-!
# A lattice of zeros forces linear characteristic growth

An entire function that vanishes at every point of an arithmetic progression `ℤ·T` carries at least
`2⌊r/(2‖T‖)⌋` zeros in the disc of radius `r`, each contributing at least `log 2` to the counting
function.  The first main theorem converts the resulting linear lower bound for `N(r, 0, g)` into one
for the characteristic of `g`.

* `logCounting_zero_ge_of_lattice_zeros` — the counting bound;
* `characteristic_ge_of_lattice_zeros` — the characteristic bound.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Metric Real Set Filter ValueDistribution MeromorphicOn Function

/-- The lattice points inside the disc of radius `r`, excluding the origin. -/
private noncomputable def latticeIndices (r : ℝ) (T : ℂ) : Finset ℤ :=
  (Finset.Icc (-(⌊r / (2 * ‖T‖)⌋₊ : ℤ)) (⌊r / (2 * ‖T‖)⌋₊ : ℤ)).erase 0

private theorem card_latticeIndices (r : ℝ) (T : ℂ) :
    (latticeIndices r T).card = 2 * ⌊r / (2 * ‖T‖)⌋₊ := by
  classical
  set N : ℕ := ⌊r / (2 * ‖T‖)⌋₊ with hN
  have hmem : (0 : ℤ) ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    simp [Finset.mem_Icc]
  rw [latticeIndices, Finset.card_erase_of_mem hmem, Int.card_Icc]
  omega

/-- **A lattice of zeros forces linear growth of the counting function.**  Every lattice point of
modulus at most `r/2` contributes at least `log 2`, and there are at least `r/‖T‖ - 2` of them. -/
theorem logCounting_zero_ge_of_lattice_zeros {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g Set.univ) (hgo : ∀ z, meromorphicOrderAt g z ≠ ⊤)
    {T : ℂ} (hT : T ≠ 0) (hzero : ∀ n : ℤ, g ((n : ℂ) * T) = 0)
    {r : ℝ} (hr1 : 1 ≤ r) :
    Real.log 2 * (r / ‖T‖ - 2) ≤ ValueDistribution.logCounting g 0 r := by
  classical
  have hTpos : (0 : ℝ) < ‖T‖ := norm_pos_iff.mpr hT
  set N : ℕ := ⌊r / (2 * ‖T‖)⌋₊ with hN
  set F : Finset ℤ := latticeIndices r T with hF
  have hNle : (N : ℝ) ≤ r / (2 * ‖T‖) := Nat.floor_le (by positivity)
  have hNge : r / (2 * ‖T‖) - 1 ≤ (N : ℝ) := le_of_lt (Nat.sub_one_lt_floor _)
  -- every index is small
  have hindex : ∀ n ∈ F, ‖((n : ℂ) * T)‖ ≤ r / 2 ∧ (n : ℂ) * T ≠ 0 := by
    intro n hn
    have hn0 : n ≠ 0 := Finset.ne_of_mem_erase hn
    have hnIcc : n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := Finset.mem_of_mem_erase hn
    rw [Finset.mem_Icc] at hnIcc
    have habs : |(n : ℝ)| ≤ (N : ℝ) := by
      rw [abs_le]
      constructor
      · exact_mod_cast hnIcc.1
      · exact_mod_cast hnIcc.2
    constructor
    · rw [norm_mul, norm_intCast]
      calc |(n : ℝ)| * ‖T‖ ≤ (N : ℝ) * ‖T‖ := by nlinarith [hTpos]
        _ ≤ (r / (2 * ‖T‖)) * ‖T‖ := by nlinarith [hTpos]
        _ = r / 2 := by field_simp
    · intro hcon
      rcases mul_eq_zero.mp hcon with h | h
      · exact hn0 (by exact_mod_cast h)
      · exact hT h
  -- the divisor supported on the lattice points
  set D₀ : Function.locallyFinsupp ℂ ℤ :=
    ∑ n ∈ F, Function.locallyFinsuppWithin.single ((n : ℂ) * T) 1 with hD₀
  have hinj : ∀ m n : ℤ, (m : ℂ) * T = (n : ℂ) * T → m = n := by
    intro m n hmn
    have := mul_right_cancel₀ hT hmn
    exact_mod_cast this
  -- each lattice point carries a zero of `g`
  have horder : ∀ n : ℤ, 1 ≤ divisor g Set.univ ((n : ℂ) * T) := by
    intro n
    set z : ℂ := (n : ℂ) * T with hz
    have hmem : z ∈ (Set.univ : Set ℂ) := Set.mem_univ z
    have hmero : MeromorphicOn g Set.univ := fun x _ => (hg x (Set.mem_univ x)).meromorphicAt
    rw [MeromorphicOn.divisor_apply hmero hmem]
    have hne : meromorphicOrderAt g z ≠ ⊤ := hgo z
    have hanal : AnalyticAt ℂ g z := hg z hmem
    have hz' : z = (n : ℂ) * T := hz
    have hmap : meromorphicOrderAt g z = ENat.map Nat.cast (analyticOrderAt g z) :=
      hanal.meromorphicOrderAt_eq
    have hazero : analyticOrderAt g z ≠ 0 := by
      intro hcon
      rcases analyticOrderAt_eq_zero.mp hcon with h | h
      · exact h hanal
      · exact h (by simpa [hz] using hzero n)
    have hatop : analyticOrderAt g z ≠ ⊤ := by
      intro hcon
      apply hne
      rw [hmap, hcon]
      rfl
    obtain ⟨k, hk⟩ : ∃ k : ℕ, analyticOrderAt g z = (k : ℕ∞) := by
      cases h : analyticOrderAt g z with
      | top => exact absurd h hatop
      | coe k => exact ⟨k, rfl⟩
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · rw [h] at hk
        exact absurd (by simpa using hk) hazero
      · exact h
    rw [hmap, hk]
    simp only [ENat.map_coe]
    rw [WithTop.untop₀_coe]
    exact_mod_cast hk1
  have hD₀le : D₀ ≤ (divisor g Set.univ)⁺ := by
    intro z
    have hsum : D₀ z = ∑ n ∈ F, (if z = (n : ℂ) * T then (1 : ℤ) else 0) := by
      rw [hD₀]
      simp only [Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply,
        Function.locallyFinsuppWithin.single_apply]
    rw [hsum]
    by_cases hex : ∃ n ∈ F, z = (n : ℂ) * T
    · obtain ⟨n, hnF, rfl⟩ := hex
      have hone : ∑ m ∈ F, (if (n : ℂ) * T = (m : ℂ) * T then (1 : ℤ) else 0) = 1 := by
        rw [Finset.sum_eq_single n]
        · simp
        · intro m _ hmn
          rw [if_neg]
          intro hcon
          exact hmn (hinj n m hcon).symm
        · intro hcon
          exact absurd hnF hcon
      rw [hone]
      have := horder n
      have hpos : (divisor g Set.univ)⁺ ((n : ℂ) * T)
          = max (divisor g Set.univ ((n : ℂ) * T)) 0 := rfl
      rw [hpos]
      exact le_max_of_le_left this
    · push_neg at hex
      have hzero' : ∑ n ∈ F, (if z = (n : ℂ) * T then (1 : ℤ) else 0) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro n hn
        rw [if_neg (hex n hn)]
      rw [hzero']
      exact posPart_nonneg _
  -- the counting function of the lattice divisor
  have hcount : Function.locallyFinsuppWithin.logCounting D₀ r
      = ∑ n ∈ F, (Real.log r - Real.log ‖((n : ℂ) * T)‖) := by
    rw [hD₀, map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl ?_
    intro n hn
    have hle : ‖((n : ℂ) * T)‖ ≤ r := le_trans (hindex n hn).1 (by linarith)
    rw [Function.locallyFinsuppWithin.logCounting_single_eq_log_sub_const hle]
    simp
  have hterm : ∀ n ∈ F, Real.log 2 ≤ Real.log r - Real.log ‖((n : ℂ) * T)‖ := by
    intro n hn
    obtain ⟨hle, hne⟩ := hindex n hn
    have hpos : 0 < ‖((n : ℂ) * T)‖ := norm_pos_iff.mpr hne
    rw [← Real.log_div (by linarith) (ne_of_gt hpos)]
    refine Real.log_le_log (by norm_num) ?_
    rw [le_div_iff₀ hpos]
    linarith
  have hlow : Real.log 2 * (2 * (N : ℝ))
      ≤ Function.locallyFinsuppWithin.logCounting D₀ r := by
    rw [hcount]
    calc Real.log 2 * (2 * (N : ℝ)) = ∑ _n ∈ F, Real.log 2 := by
          rw [Finset.sum_const, hF, card_latticeIndices, ← hN, nsmul_eq_mul]
          push_cast
          ring
      _ ≤ ∑ n ∈ F, (Real.log r - Real.log ‖((n : ℂ) * T)‖) := Finset.sum_le_sum hterm
  -- compare with the counting function of `g`
  have hgcount : ValueDistribution.logCounting g 0 r
      = Function.locallyFinsuppWithin.logCounting (divisor g Set.univ)⁺ r := by
    simp [ValueDistribution.logCounting]
  have hcompare := Function.locallyFinsuppWithin.logCounting_le hD₀le hr1
  rw [← hgcount] at hcompare
  have hNbig : r / ‖T‖ - 2 ≤ 2 * (N : ℝ) := by
    have h : r / (2 * ‖T‖) = (r / ‖T‖) / 2 := by
      rw [div_div]
      ring_nf
    rw [h] at hNge
    linarith
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  calc Real.log 2 * (r / ‖T‖ - 2) ≤ Real.log 2 * (2 * (N : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hNbig hlog2
    _ ≤ Function.locallyFinsuppWithin.logCounting D₀ r := hlow
    _ ≤ ValueDistribution.logCounting g 0 r := hcompare

/-- **A lattice of zeros forces linear growth of the characteristic.**  The first main theorem turns
the counting bound into a bound for the characteristic, at the cost of one additive constant. -/
theorem exists_characteristic_ge_of_lattice_zeros {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g Set.univ) (hgo : ∀ z, meromorphicOrderAt g z ≠ ⊤)
    {T : ℂ} (hT : T ≠ 0) (hzero : ∀ n : ℤ, g ((n : ℂ) * T) = 0) :
    ∃ K : ℝ, ∀ r : ℝ, 1 ≤ r →
      Real.log 2 * (r / ‖T‖ - 2) - K ≤ ValueDistribution.characteristic g ⊤ r := by
  refine ⟨max |Real.log ‖g 0‖| |Real.log ‖meromorphicTrailingCoeffAt g 0‖|, ?_⟩
  intro r hr
  have hmero : Meromorphic g := fun z => (hg z (Set.mem_univ z)).meromorphicAt
  have h1 := logCounting_zero_ge_of_lattice_zeros hg hgo hT hzero hr
  have hinv : ValueDistribution.logCounting g 0 r = ValueDistribution.logCounting g⁻¹ ⊤ r :=
    (congrFun (ValueDistribution.logCounting_inv (f := g)) r).symm
  have hsplit : ValueDistribution.characteristic g⁻¹ ⊤ r
      = ValueDistribution.proximity g⁻¹ ⊤ r + ValueDistribution.logCounting g⁻¹ ⊤ r := rfl
  have hp : 0 ≤ ValueDistribution.proximity g⁻¹ ⊤ r := by
    have := ValueDistribution.proximity_nonneg (f := g⁻¹) (a := ⊤)
    exact this r
  have h2 : ValueDistribution.logCounting g 0 r ≤ ValueDistribution.characteristic g⁻¹ ⊤ r := by
    rw [hinv, hsplit]
    linarith
  have h3 := ValueDistribution.characteristic_sub_characteristic_inv_le (f := g) (R := r) hmero
  have h4 := (abs_le.mp h3).1
  linarith

end GaloisForLFunctions.HTGeometry
