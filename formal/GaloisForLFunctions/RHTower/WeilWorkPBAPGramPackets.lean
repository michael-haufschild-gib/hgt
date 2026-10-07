import GaloisForLFunctions.RHTower.WeilFullConeOneSidedCriterion
import GaloisForLFunctions.RHTower.WeilDilationCriticalLineShift
import Mathlib.Analysis.Matrix.Order

/-!
# Finite Gram matrices realized by smooth Weil tests

Narrow packets centred at logarithms of integers realize every finite positive
semidefinite Gram matrix. At rational logarithms, integer log separation removes
all terms except the exact multiplicative diagonal. Thus finitely many matrix
identities certify cancellation at every integer logarithm.
-/

open Complex MeasureTheory Zeta23
open scoped BigOperators ComplexConjugate ContDiff ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator

noncomputable section

namespace RHTower.WeilWorkPBAP

open WeilOneSided

/-- The positive integer labels through `N`. -/
abbrev PacketIndex (N : ℕ) := ↥(Finset.Icc 1 N)

/-- Squared mass of the common packet at denominator resolution `L`. -/
def packetMass (N L : ℕ) : ℝ := ∫ t, (narrowBump (N * L) t) ^ 2

theorem packetMass_pos (N L : ℕ) : 0 < packetMass N L :=
  integral_narrowBump_sq_pos _

/-- A finite combination of smooth packets at logarithmic centres. -/
def gramPacket (N L : ℕ) (c : ℕ → ℂ) (u : ℝ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 N, c m * narrowBumpC (N * L) (u - resPt N m)

theorem contDiff_gramPacket (N L : ℕ) (c : ℕ → ℂ) :
    ContDiff ℝ ∞ (gramPacket N L c) := by
  exact ContDiff.sum fun _ _ => contDiff_const.mul
    ((contDiff_narrowBumpC _).comp (contDiff_id.sub contDiff_const))

theorem hasCompactSupport_gramPacket (N L : ℕ) (c : ℕ → ℂ) :
    HasCompactSupport (gramPacket N L c) := by
  have h := HasCompactSupport.finset_sum (s := Finset.Icc 1 N)
    (f := fun m u => c m * narrowBumpC (N * L) (u - resPt N m))
    (fun m _ => ((hasCompactSupport_narrowBumpC _).comp_homeomorph
      (Homeomorph.subRight (resPt N m))).mul_left)
  have heq : (∑ m ∈ Finset.Icc 1 N,
      fun u => c m * narrowBumpC (N * L) (u - resPt N m)) = gramPacket N L c := by
    funext u
    simp only [Finset.sum_apply, gramPacket]
  rwa [heq] at h

/-- The packet combination as an admissible full Weil test. -/
def gramPacketFn (N L : ℕ) (c : ℕ → ℂ) : WeilTestFn :=
  ⟨gramPacket N L c, (contDiff_gramPacket N L c).of_le (by norm_cast),
    hasCompactSupport_gramPacket N L c⟩

private theorem packet_autocorrelation_zero (M : ℕ) {y : ℝ}
    (hy : 1 / ((M : ℝ) + 1) ≤ |y|) :
    EF.weilTest (narrowBumpC M) (narrowBumpC M) y = 0 := by
  apply weilTest_self_eq_zero (fun _ h => narrowBumpC_eq_zero M h)
  have hpos : 0 < 1 / ((M : ℝ) + 1) := by positivity
  have hhalf : 2 * (1 / (4 * ((M : ℝ) + 1))) =
      (1 / ((M : ℝ) + 1)) / 2 := by field_simp; ring
  rw [hhalf]
  linarith

private theorem rational_sample_shift (N a b m k : ℕ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hm : 1 ≤ m) (hk : 1 ≤ k) :
    Real.log a - Real.log b - resPt N m + resPt N k =
      Real.log (a * k : ℕ) - Real.log (b * m : ℕ) := by
  have hlog (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
      Real.log (p * q : ℕ) = Real.log p + Real.log q := by
    rw [Nat.cast_mul, Real.log_mul]
    · exact_mod_cast (show p ≠ 0 by omega)
    · exact_mod_cast (show q ≠ 0 by omega)
  rw [hlog a k ha hk, hlog b m hb hm, resPt, resPt]
  ring

/-- Rational samples are exactly the corresponding finite multiplicative diagonal. -/
theorem gramPacket_rational_sample (N L : ℕ) (c : ℕ → ℂ)
    {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hbL : b ≤ L) :
    EF.weilTest (gramPacket N L c) (gramPacket N L c) (Real.log a - Real.log b) =
      (packetMass N L : ℂ) * ∑ m ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        if a * k = b * m then c m * conj (c k) else 0 := by
  change EF.weilTest (fun u => ∑ m ∈ Finset.Icc 1 N,
    c m * narrowBumpC (N * L) (u - resPt N m))
    (fun u => ∑ m ∈ Finset.Icc 1 N,
      c m * narrowBumpC (N * L) (u - resPt N m)) _ = _
  rw [weilTest_sum_translates (contDiff_narrowBumpC _).continuous
    (hasCompactSupport_narrowBumpC _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hm
  obtain ⟨hk1, _⟩ := Finset.mem_Icc.mp hk
  rw [rational_sample_shift N a b m k ha hb hm1 hk1]
  by_cases heq : a * k = b * m
  · rw [if_pos heq, heq, sub_self]
    change c m * conj (c k) * EF.weilTest
      (fun u => ((narrowBump (N * L) u : ℝ) : ℂ))
      (fun u => ((narrowBump (N * L) u : ℝ) : ℂ)) 0 = _
    rw [weilTest_self_zero_ofReal]
    unfold packetMass
    ring
  · rw [if_neg heq, packet_autocorrelation_zero (N * L)
      (log_gap (by nlinarith) (by nlinarith) (by nlinarith) heq)]
    simp

private def extendPacketCoeffs {N : ℕ} (c : PacketIndex N → ℂ) (m : ℕ) : ℂ :=
  if hm : m ∈ Finset.Icc 1 N then c ⟨m, hm⟩ else 0

private theorem extendPacketCoeffs_apply {N : ℕ} (c : PacketIndex N → ℂ)
    (m : PacketIndex N) : extendPacketCoeffs c m = c m := by
  simp only [extendPacketCoeffs, dif_pos m.property]

private theorem gramPacket_rational_sample_subtype (N L : ℕ)
    (c : PacketIndex N → ℂ) {a b : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hbL : b ≤ L) :
    EF.weilTest (gramPacket N L (extendPacketCoeffs c))
        (gramPacket N L (extendPacketCoeffs c)) (Real.log a - Real.log b) =
      (packetMass N L : ℂ) * ∑ m : PacketIndex N, ∑ k : PacketIndex N,
        if a * (k : ℕ) = b * (m : ℕ) then c m * conj (c k) else 0 := by
  rw [gramPacket_rational_sample N L _ ha hb hbL]
  simp_rw [Finset.sum_subtype (p := fun m : ℕ => m ∈ Finset.Icc 1 N)
    (Finset.Icc 1 N) (fun _ => Iff.rfl), extendPacketCoeffs_apply]

private theorem exists_packet_coeffs {N : ℕ}
    (A : Matrix (PacketIndex N) (PacketIndex N) ℂ) (hA : A.PosSemidef) :
    ∃ c : PacketIndex N → PacketIndex N → ℂ,
      ∀ m k, (∑ i, c i m * conj (c i k)) = A m k := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  refine ⟨fun i m => conj (B i m), fun m k => ?_⟩
  rw [hB, Matrix.star_eq_conjTranspose, Matrix.mul_apply]
  simp

/-- Every finite positive Gram matrix has a smooth test realization with exact rational samples.
The numerator is unrestricted; only the denominator resolution is fixed. -/
theorem exists_gramPacket_realization (N L : ℕ)
    (A : {A : Matrix (PacketIndex N) (PacketIndex N) ℂ // A.PosSemidef}) :
    ∃ f : PacketIndex N → WeilTestFn,
      (∀ i, ContDiff ℝ ∞ (f i).1) ∧
      ∀ (a b : ℕ), 1 ≤ a → 1 ≤ b → b ≤ L →
        (∑ i, EF.weilTest (f i).1 (f i).1 (Real.log a - Real.log b)) =
          (packetMass N L : ℂ) * ∑ m : PacketIndex N, ∑ k : PacketIndex N,
            if a * (k : ℕ) = b * (m : ℕ) then A.1 m k else 0 := by
  obtain ⟨c, hc⟩ := exists_packet_coeffs A.1 A.2
  refine ⟨fun i => gramPacketFn N L (extendPacketCoeffs (c i)),
    fun i => contDiff_gramPacket N L _, ?_⟩
  intro a b ha hb hbL
  change (∑ i, EF.weilTest (gramPacket N L (extendPacketCoeffs (c i)))
    (gramPacket N L (extendPacketCoeffs (c i))) _) = _
  simp_rw [gramPacket_rational_sample_subtype N L _ ha hb hbL]
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases heq : a * (k : ℕ) = b * (m : ℕ)
  · simp only [if_pos heq]
    exact hc m k
  · simp only [if_neg heq, Finset.sum_const_zero]

/-- A multiplicative diagonal of a matrix on the positive integer labels. -/
def divisibilityTrace {N : ℕ} (A : Matrix (PacketIndex N) (PacketIndex N) ℂ)
    (n : ℕ) : ℂ :=
  ∑ m : PacketIndex N, ∑ k : PacketIndex N,
    if n * (k : ℕ) = (m : ℕ) then A m k else 0

theorem divisibilityTrace_eq_zero_above {N n : ℕ}
    (A : Matrix (PacketIndex N) (PacketIndex N) ℂ) (hn : N < n) :
    divisibilityTrace A n = 0 := by
  apply Finset.sum_eq_zero
  intro m _
  apply Finset.sum_eq_zero
  intro k _
  have hmN := (Finset.mem_Icc.mp m.property).2
  have hk1 := (Finset.mem_Icc.mp k.property).1
  have hne : n * (k : ℕ) ≠ (m : ℕ) := by nlinarith
  exact if_neg hne

/-- Positive Gram matrices with zero nontrivial divisibility diagonals through their size. -/
def NullPacketGram (N : ℕ) :=
  {A : Matrix (PacketIndex N) (PacketIndex N) ℂ //
    A.PosSemidef ∧ ∀ n ∈ Finset.Icc 2 N, divisibilityTrace A n = 0}

/-- Finitely many matrix identities give smooth finite mixtures null at every positive
integer logarithm. The same family also retains its exact bounded-denominator rational samples. -/
theorem exists_nullPacket_realization (N L : ℕ) (A : NullPacketGram N) :
    ∃ f : PacketIndex N → WeilTestFn,
      (∀ i, ContDiff ℝ ∞ (f i).1) ∧
      (∀ n : ℕ, 2 ≤ n → ∑ i, EF.weilTest (f i).1 (f i).1 (Real.log n) = 0) ∧
      ∀ (a b : ℕ), 1 ≤ a → 1 ≤ b → b ≤ L + 1 →
        (∑ i, EF.weilTest (f i).1 (f i).1 (Real.log a - Real.log b)) =
          (packetMass N (L + 1) : ℂ) * ∑ m : PacketIndex N, ∑ k : PacketIndex N,
            if a * (k : ℕ) = b * (m : ℕ) then A.1 m k else 0 := by
  obtain ⟨f, hf, hs⟩ := exists_gramPacket_realization N (L + 1) ⟨A.1, A.2.1⟩
  refine ⟨f, hf, ?_, hs⟩
  intro n hn
  have hzero : divisibilityTrace A.1 n = 0 := by
    by_cases hnN : n ≤ N
    · exact A.2.2 n (Finset.mem_Icc.mpr ⟨hn, hnN⟩)
    · exact divisibilityTrace_eq_zero_above A.1 (by omega)
  have h := hs n 1 (by omega) le_rfl (by omega)
  simp only [Nat.cast_one, Real.log_one, sub_zero, one_mul] at h
  change _ = (packetMass N (L + 1) : ℂ) * divisibilityTrace A.1 n at h
  rwa [hzero, mul_zero] at h

/-- Unit weights on the realized tests; coincident tests have their weights added. -/
def packetMixture {N : ℕ} (f : PacketIndex N → WeilTestFn) : WeilTestFn →₀ ℝ :=
  ∑ i, Finsupp.single (f i) 1

theorem packetMixture_nonneg {N : ℕ} (f : PacketIndex N → WeilTestFn)
    (g : WeilTestFn) : 0 ≤ packetMixture f g := by
  have h : 0 ≤ packetMixture f := Finset.sum_nonneg
    (fun i _ => Finsupp.single_nonneg.mpr (show (0 : ℝ) ≤ 1 by positivity))
  exact h g

theorem packetMixture_sum {N : ℕ} (f : PacketIndex N → WeilTestFn)
    (F : WeilTestFn → ℝ) :
    (packetMixture f).sum (fun g t => t * F g) = ∑ i, F (f i) := by
  change (Finsupp.linearCombination ℝ F) (packetMixture f) = _
  rw [packetMixture, map_sum]
  simp only [Finsupp.linearCombination_single, one_smul]

private theorem sum_logValue_eq_zero {N : ℕ} (f : PacketIndex N → WeilTestFn)
    (n : ℕ) (hn : ∑ i, EF.weilTest (f i).1 (f i).1 (Real.log n) = 0) :
    ∑ i, logValue (f i).1 n = 0 := by
  unfold logValue
  rw [← Finset.sum_div, ← Complex.re_sum, Finset.sum_add_distrib, hn]
  simp only [weilTest_self_neg, ← map_sum, hn, map_zero, zero_add,
    Complex.zero_re, zero_div]

/-- Exact admissibility in the full PBAP mixture cone, with its mass and every rational
sample retained. The theorem assumes no positivity principle for the Weil energy. -/
theorem exists_nullPacket_mixture (N L : ℕ) (A : NullPacketGram N) :
    ∃ f : PacketIndex N → WeilTestFn,
      (∀ i, ContDiff ℝ ∞ (f i).1) ∧
      (∀ g, 0 ≤ packetMixture f g) ∧
      (∀ n : ℕ, 2 ≤ n →
        (packetMixture f).sum (fun g t => t * logValue g.1 n) = 0) ∧
      (∑ i, EF.weilTest (f i).1 (f i).1 0) =
        (packetMass N (L + 1) : ℂ) * A.1.trace ∧
      ∀ (a b : ℕ), 1 ≤ a → 1 ≤ b → b ≤ L + 1 →
        (∑ i, EF.weilTest (f i).1 (f i).1 (Real.log a - Real.log b)) =
          (packetMass N (L + 1) : ℂ) * ∑ m : PacketIndex N, ∑ k : PacketIndex N,
            if a * (k : ℕ) = b * (m : ℕ) then A.1 m k else 0 := by
  obtain ⟨f, hf, hn, hs⟩ := exists_nullPacket_realization N L A
  refine ⟨f, hf, packetMixture_nonneg f, ?_, ?_, hs⟩
  · intro n hn2
    rw [packetMixture_sum]
    exact sum_logValue_eq_zero f n (hn n hn2)
  · have h := hs 1 1 le_rfl le_rfl (by omega)
    simpa only [sub_self, one_mul, ← Subtype.ext_iff, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Matrix.trace, Matrix.diag] using h

end RHTower.WeilWorkPBAP
