import GaloisForLFunctions.RHTower.EvenSectorDetunedToeplitz
import GaloisForLFunctions.RHTower.EvenSectorDoublePoleExclusion

/-!
# Source uniqueness for every finite even pole weight

Detuned reflection admits signed arithmetic coefficients on the even pole-free
cone. This eliminates the negative-superpole alternative without imposing any
growth, convergence, sign, or Abel-limit condition on the source. The existing
double-pole exclusion then identifies every source in every finite even cone.

The theorem classifies sources; it does not assert that these cones are inhabited.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate
open Zeta23

noncomputable section
namespace RHTower.EvenSector
open WeilMeanSquare OddSector Detuned

/-- Every finite signed arithmetic correlation has an even, pole-free realization.
This construction has no positivity or source hypothesis. -/
theorem signed_arithmetic_evenization (N : ℕ) (c : ℕ → ℝ) :
    ∃ k : ℝ, 0 < k ∧ ∃ F : ℝ → ℂ,
      ContDiff ℝ 2 F ∧ HasCompactSupport F ∧ (∀ u, F (-u) = F u) ∧
      paperFT F (I / 2) = 0 ∧
      ∀ n : ℕ, 1 ≤ n →
        EF.weilTest F F (Real.log n) = (k : ℂ) *
          ((∑ m ∈ Finset.Icc 1 (N + 1),
            if n * m ≤ N + 1 then c (n * m) * c m else 0 : ℝ) : ℂ) ∧
        EF.weilTest F F (-Real.log n) = (k : ℂ) *
          ((∑ m ∈ Finset.Icc 1 (N + 1),
            if n * m ≤ N + 1 then c (n * m) * c m else 0 : ℝ) : ℂ) := by
  let w := width (N + 1)
  let d : ℕ → ℝ := fun m => if m ≤ N + 1 then c m else 0
  let k0 : ℝ := ∫ u, ResonatorProfile.gR w u ^ 2
  have hw : 0 < w := width_pos _
  have hk : 0 < k0 := lt_of_lt_of_le
    (div_pos ResonatorProfile.integral_d2_sq_pos (by positivity))
    (ResonatorProfile.integral_gR_sq_ge hw)
  have hd : ∀ m, N + 1 < m → d m = 0 := fun m hm => by simp [d, Nat.not_le.mpr hm]
  have hg := (ResonatorProfile.contDiff_gC w 2).continuous
  have hgc := hasCompactSupport_gC hw
  have hvan : ∀ y, width (N + 1) ≤ |y| →
      EF.weilTest (ResonatorProfile.gC w) (ResonatorProfile.gC w) y = 0 := fun y hy =>
    weilTest_self_eq_zero (fun u hu => gC_eq_zero hw hu) (by change w ≤ |y| at hy; linarith)
  have hk0 : EF.weilTest (ResonatorProfile.gC w) (ResonatorProfile.gC w) 0 = (k0 : ℂ) :=
    weilTest_self_zero_ofReal
  refine ⟨2 * k0, by positivity, packet (N + 1) d (ResonatorProfile.gC w),
    contDiff_packet (ResonatorProfile.contDiff_gC w 2), hasCompactSupport_packet hgc, ?_, ?_, ?_⟩
  · exact packet_neg fun u => by
      change (ResonatorProfile.gR w (-u) : ℂ) = (ResonatorProfile.gR w u : ℂ)
      rw [gR_neg]
  · rw [paperFT_packet hg hgc, (ResonatorProfile.paperFT_gC_pole hw).1, mul_zero]
  · intro n hn
    have hsum : (∑ m ∈ Finset.Icc 1 (N + 1), d (n * m) * d m) =
        ∑ m ∈ Finset.Icc 1 (N + 1), if n * m ≤ N + 1 then c (n * m) * c m else 0 := by
      refine Finset.sum_congr rfl fun m hm => ?_
      simp only [d, if_pos (Finset.mem_Icc.mp hm).2]
      split_ifs <;> simp
    constructor
    · rw [weilTest_packet_log (by omega) hg hgc hvan hd hn, hk0, hsum]
      push_cast
      ring
    · rw [weilTest_packet_neg_log (by omega) hg hgc hvan hd hn, hk0, hsum]
      push_cast
      ring

private theorem signed_primitive_square {lam : ℕ → ℝ}
    (h : WeilPositiveEvenPolar lam) {N : ℕ} (hN : 1 ≤ N) :
    0 ≤ 4 * Real.log N + toeplitzConstant ∧
      ∀ S : Finset ℕ, S ⊆ Finset.Icc 2 N → IsPrimitiveSet S →
        ∑ n ∈ S, lam n ^ 2 / n ≤ (4 * Real.log N + toeplitzConstant) ^ 2 := by
  have key : ∀ S : Finset ℕ, S ⊆ Finset.Icc 2 N → IsPrimitiveSet S →
      ∀ t : ℝ, 2 * t * ∑ n ∈ S, lam n ^ 2 / n ≤
        (4 * Real.log N + toeplitzConstant) * (1 + t ^ 2 * ∑ n ∈ S, lam n ^ 2 / n) := by
    intro S hS hprim t
    set c : ℕ → ℝ := fun m => if m = 1 then 1 else if m ∈ S then t * lam m / Real.sqrt m else 0
      with hc
    have hcN : ∀ m, N < m → c m = 0 := by
      intro m hm
      have h1 : m ≠ 1 := by omega
      have h2 : m ∉ S := fun h' => by have := (Finset.mem_Icc.mp (hS h')).2; omega
      simp [hc, h1, h2]
    have hb := signed_toeplitz h hN c hcN
    have hinner : ∀ n ∈ Finset.Icc 2 N,
        ∑ m ∈ Finset.Icc 1 N, c (n * m) * c m = if n ∈ S then t * lam n / Real.sqrt n else 0 := by
      intro n hn
      obtain ⟨hn2, hnN⟩ := Finset.mem_Icc.mp hn
      rw [← Finset.add_sum_erase _ _ (Finset.mem_Icc.mpr ⟨le_rfl, hN⟩)]
      have hrest : ∑ m ∈ (Finset.Icc 1 N).erase 1, c (n * m) * c m = 0 := by
        refine Finset.sum_eq_zero fun m hm => ?_
        obtain ⟨hm1, hmI⟩ := Finset.mem_erase.mp hm
        by_cases hmS : m ∈ S
        · have hnm1 : n * m ≠ 1 := by
            have := (Finset.mem_Icc.mp hmI).1; nlinarith
          have hnmS : n * m ∉ S := fun h' => hprim _ h' m hmS n hn2 rfl
          simp [hc, hnm1, hnmS]
        · simp [hc, hm1, hmS]
      rw [hrest, add_zero, mul_one]
      have hn1 : n ≠ 1 := by omega
      by_cases hnS : n ∈ S <;> simp [hc, hn1, hnS]
    have hmass : ∑ m ∈ Finset.Icc 1 N, c m ^ 2 = 1 + t ^ 2 * ∑ n ∈ S, lam n ^ 2 / n := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_Icc.mpr ⟨le_rfl, hN⟩)]
      have hS' : S ⊆ (Finset.Icc 1 N).erase 1 := fun n hn => by
        have := Finset.mem_Icc.mp (hS hn)
        exact Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr ⟨by omega, this.2⟩⟩
      rw [← Finset.sum_subset hS' (fun m hm hmS => by
        have hm1 := (Finset.mem_erase.mp hm).1
        simp [hc, hm1, hmS]), Finset.mul_sum]
      congr 1
      · simp [hc]
      · refine Finset.sum_congr rfl fun n hn => ?_
        have hn2 := (Finset.mem_Icc.mp (hS hn)).1
        have hn1 : n ≠ 1 := by omega
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
        simp only [hc, hn1, hn, if_false, if_true, div_pow, mul_pow, Real.sq_sqrt hn0.le]
        ring
    have hlhs : ∑ n ∈ Finset.Icc 2 N, lam n / Real.sqrt n *
        ∑ m ∈ Finset.Icc 1 N, c (n * m) * c m = t * ∑ n ∈ S, lam n ^ 2 / n := by
      rw [Finset.sum_congr rfl fun n hn => by rw [hinner n hn], Finset.mul_sum]
      rw [← Finset.sum_subset hS (fun n _ hnS => by simp [hnS])]
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn2 := (Finset.mem_Icc.mp (hS hn)).1
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
      rw [if_pos hn, show lam n / Real.sqrt n * (t * lam n / Real.sqrt n) =
        t * (lam n ^ 2 / (Real.sqrt n * Real.sqrt n)) by ring, hsq]
    rw [hlhs, hmass] at hb
    linarith
  have hB : 0 ≤ 4 * Real.log N + toeplitzConstant := by
    have := key ∅ (Finset.empty_subset _) (fun m hm => absurd hm (Finset.notMem_empty m)) 0
    simpa using this
  refine ⟨hB, fun S hS hprim => ?_⟩
  set Q := ∑ n ∈ S, lam n ^ 2 / n with hQ
  set B := 4 * Real.log N + toeplitzConstant with hBdef
  rcases hB.eq_or_lt with he | hp
  · have hh := key S hS hprim 1
    rw [← he] at hh
    nlinarith [Finset.sum_nonneg (fun n (_ : n ∈ S) =>
      div_nonneg (sq_nonneg (lam n)) (Nat.cast_nonneg n))]
  · have hh := key S hS hprim (1 / B)
    change 2 * (1 / B) * Q ≤ B * (1 + (1 / B) ^ 2 * Q) at hh
    have he1 : B * (1 + (1 / B) ^ 2 * Q) = B + Q / B := by field_simp
    have he2 : 2 * (1 / B) * Q = 2 * (Q / B) := by ring
    rw [he1, he2] at hh
    have hq : Q / B ≤ B := by linarith
    have hq' := (div_le_iff₀ hp).mp hq
    nlinarith only [hq']

private theorem signed_block_square {lam : ℕ → ℝ} (h : WeilPositiveEvenPolar lam)
    {N : ℕ} (hN : 1 ≤ N) :
    0 ≤ 4 * Real.log (2 * N : ℕ) + toeplitzConstant ∧
      ∑ n ∈ Finset.Ioc N (2 * N), lam n ^ 2 ≤
        (2 * N : ℕ) * (4 * Real.log (2 * N : ℕ) + toeplitzConstant) ^ 2 := by
  obtain ⟨hB, hS⟩ := signed_primitive_square h (N := 2 * N) (by omega)
  refine ⟨hB, ?_⟩
  let S := Finset.Ioc N (2 * N)
  have hsub : S ⊆ Finset.Icc 2 (2 * N) := fun n hn => by
    obtain ⟨_, _⟩ := Finset.mem_Ioc.mp hn
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hprim : IsPrimitiveSet S := by
    intro m hm m' hm' k hk heq
    obtain ⟨_, _⟩ := Finset.mem_Ioc.mp hm
    obtain ⟨_, _⟩ := Finset.mem_Ioc.mp hm'
    have : k * m' ≥ 2 * (N + 1) := Nat.mul_le_mul hk (by omega)
    omega
  have hQ := hS S hsub hprim
  have h2N : (0 : ℝ) < (2 * N : ℕ) := by exact_mod_cast (show 0 < 2 * N by omega)
  calc ∑ n ∈ S, lam n ^ 2
      = (2 * N : ℕ) * ∑ n ∈ S, lam n ^ 2 / (2 * N : ℕ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun n _ => by field_simp
    _ ≤ (2 * N : ℕ) * ∑ n ∈ S, lam n ^ 2 / n := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun n hn => ?_) h2N.le
        obtain ⟨hn1, hn2⟩ := Finset.mem_Ioc.mp hn
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
        exact div_le_div_of_nonneg_left (sq_nonneg _) hn0 (by exact_mod_cast hn2)
    _ ≤ (2 * N : ℕ) * (4 * Real.log (2 * N : ℕ) + toeplitzConstant) ^ 2 :=
        mul_le_mul_of_nonneg_left hQ h2N.le

/-- The negative-superpole branch is impossible already on the even pole-free cone. -/
theorem summable_abs_div_rpow_of_weilPositiveEvenPolar {lam : ℕ → ℝ}
    (h : WeilPositiveEvenPolar lam) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ := by
  refine summable_div_rpow_of_block (fun n => abs_nonneg (lam n))
    (B := 3 / 2 * (5 + |toeplitzConstant|)) (j₀ := 0) hσ fun j _ => ?_
  obtain ⟨hB, hsq⟩ := signed_block_square h (N := 2 ^ j) Nat.one_le_two_pow
  have hpos := sum_abs_Ioc_le_of_sum_sq hB hsq
  rw [show 2 * 2 ^ j = 2 ^ (j + 1) by ring] at hpos
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hlog : Real.log ((2 ^ (j + 1) : ℕ) : ℝ) ≤ (j : ℝ) + 1 := by
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    have := Real.log_two_lt_d9
    push_cast
    nlinarith
  have hcast : ((2 ^ j : ℕ) : ℝ) = (2 : ℝ) ^ j := by push_cast; ring
  rw [hcast] at hpos
  have ht : 4 * Real.log ((2 ^ (j + 1) : ℕ) : ℝ) + toeplitzConstant + 1 ≤
      (5 + |toeplitzConstant|) * ((j : ℝ) + 1) := by
    nlinarith [le_abs_self toeplitzConstant, abs_nonneg toeplitzConstant]
  have hpos' := hpos.trans (mul_le_mul_of_nonneg_left ht (by positivity))
  nlinarith

/-- Every arithmetic source in any finite even pole-weight cone is canonical.
No sign, growth, convergence, or Abel-limit premise is required. -/
theorem source_unique_of_weilPositiveEvenAt {β : ℝ} {lam : ℕ → ℝ}
    (h : WeilPositiveEvenAt β lam) :
    ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := by
  have hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ :=
    fun _ hσ => summable_abs_div_rpow_of_weilPositiveEvenPolar
      (weilPositiveEvenPolar_of_weilPositiveEvenAt h) hσ
  exact (riemannHypothesis_of_weilPositiveEvenAt_of_abel h hsl
    (no_negative_double_pole_of_weilPositiveEvenAt h hsl)).2

/-- The union of all finite even pole-weight source cones has at most one source,
on precisely the arithmetic coordinates used by the Weil functional. -/
theorem even_pole_weight_sources_subsingleton :
    ∀ (β γ : ℝ) (lam mu : ℕ → ℝ),
      WeilPositiveEvenAt β lam → WeilPositiveEvenAt γ mu →
        ∀ n, 2 ≤ n → lam n = mu n := by
  intro β γ lam mu hlam hmu n hn
  exact (source_unique_of_weilPositiveEvenAt hlam n hn).trans
    (source_unique_of_weilPositiveEvenAt hmu n hn).symm

end RHTower.EvenSector
end
