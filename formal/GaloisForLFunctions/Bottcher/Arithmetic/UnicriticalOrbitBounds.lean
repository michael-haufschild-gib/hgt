import GaloisForLFunctions.Bottcher.Dynamics
import GaloisForLFunctions.HTGeometry.RittUnicriticalNoCocycle
import Mathlib.Tactic

/-!
# Sharp bounds for bounded unicritical critical orbits

On the compact closure of a bounded critical orbit, choose a point of maximal
modulus `R`. Forward invariance and the reverse triangle inequality give
`R^(d+2) ≤ 2R`. This proves the degree-dependent escape bound for bounded
orbits, extending the finite-orbit argument in Sano, Lemma 3.2.
-/

noncomputable section
namespace Bottcher.Arithmetic
open GaloisForLFunctions.HTGeometry Set Bornology

/-- The monic unicritical map of degree `d+2`. -/
def unicriticalMap {K : Type*} [Field K] (d : ℕ) (c : K) : K → K :=
  (unicriticalPoly (d + 2) 1 c).eval

@[simp] theorem unicriticalMap_apply {K : Type*} [Field K] (d : ℕ) (c z : K) :
    unicriticalMap d c z = z ^ (d + 2) + c := by
  simp only [unicriticalMap, unicriticalPoly_eval, one_mul]

/-- Forward orbit of the unique finite critical point. -/
def criticalOrbit {K : Type*} [Field K] (d : ℕ) (c : K) (n : ℕ) : K :=
  (unicriticalMap d c)^[n] 0

@[simp] theorem criticalOrbit_zero {K : Type*} [Field K] (d : ℕ) (c : K) :
    criticalOrbit d c 0 = 0 := rfl

@[simp] theorem criticalOrbit_succ {K : Type*} [Field K] (d : ℕ) (c : K) (n : ℕ) :
    criticalOrbit d c (n + 1) = criticalOrbit d c n ^ (d + 2) + c := by
  simp only [criticalOrbit, Function.iterate_succ_apply', unicriticalMap_apply]

@[simp] theorem criticalOrbit_one {K : Type*} [Field K] (d : ℕ) (c : K) :
    criticalOrbit d c 1 = c := by simp only [criticalOrbit_succ, criticalOrbit_zero,
      zero_pow (by omega : d + 2 ≠ 0), zero_add]

/-- Boundedness is equivalent to the sharp power bound at every critical iterate. -/
theorem bounded_criticalOrbit_iff (d : ℕ) (c : ℂ) :
    IsBounded (range (criticalOrbit d c)) ↔
      ∀ n : ℕ, ‖criticalOrbit d c n‖ ^ (d + 1) ≤ 2 := by
  constructor
  · intro hbounded
    have hzero : (0 : ℂ) ∈ closure (range (criticalOrbit d c)) :=
      subset_closure ⟨0, criticalOrbit_zero d c⟩
    obtain ⟨z, hz, hmax⟩ := hbounded.isCompact_closure.exists_isMaxOn
      ⟨0, hzero⟩ continuous_norm.continuousOn
    have hforward : MapsTo (unicriticalMap d c) (range (criticalOrbit d c))
        (range (criticalOrbit d c)) := by
      rintro w ⟨n, rfl⟩
      refine ⟨n + 1, ?_⟩
      rw [criticalOrbit_succ, unicriticalMap_apply]
    have hcontinuous : Continuous (unicriticalMap d c : ℂ → ℂ) := by
      have he : unicriticalMap d c = (fun z : ℂ => z ^ (d + 2) + c) :=
        funext (unicriticalMap_apply d c)
      rw [he]
      fun_prop
    have hnext := hmax ((hforward.closure hcontinuous) hz)
    have hc := hmax (subset_closure (show c ∈ range (criticalOrbit d c) from
      ⟨1, criticalOrbit_one d c⟩))
    have hreverse := norm_sub_norm_le (z ^ (d + 2)) (-c)
    simp only [norm_neg, sub_neg_eq_add, norm_pow] at hreverse
    rw [unicriticalMap_apply] at hnext
    change ‖z ^ (d + 2) + c‖ ≤ ‖z‖ at hnext
    change ‖c‖ ≤ ‖z‖ at hc
    have hpower : ‖z‖ ^ (d + 2) ≤ 2 * ‖z‖ := by
      linarith only [hreverse, hnext, hc]
    have htop : ‖z‖ ^ (d + 1) ≤ 2 := by
      by_cases hz0 : z = 0
      · simp only [hz0, norm_zero, zero_pow (by omega : d + 1 ≠ 0)]
        norm_num
      · have hp := norm_pos_iff.mpr hz0
        rw [show d + 2 = (d + 1) + 1 by omega, pow_succ] at hpower
        nlinarith only [hpower, hp]
    intro n
    exact (pow_le_pow_left₀ (norm_nonneg _) (hmax (subset_closure ⟨n, rfl⟩))
      (d + 1)).trans htop
  · intro h
    rw [isBounded_iff_forall_norm_le]
    refine ⟨2, ?_⟩
    rintro z ⟨n, rfl⟩
    by_cases hn : ‖criticalOrbit d c n‖ ≤ 1
    · linarith only [hn]
    · exact (le_self_pow₀ (le_of_not_ge hn) (by omega : d + 1 ≠ 0)).trans (h n)

/-- A critical orbit is infinite or satisfies the sharp escape bound everywhere. -/
theorem criticalOrbit_infinite_or_power_bound (d : ℕ) (c : ℂ) :
    (range (criticalOrbit d c)).Infinite ∨
      ∀ n : ℕ, ‖criticalOrbit d c n‖ ^ (d + 1) ≤ 2 := by
  by_cases h : (range (criticalOrbit d c)).Finite
  · exact Or.inr ((bounded_criticalOrbit_iff d c).mp h.isBounded)
  · exact Or.inl h

/-- Field embeddings preserve every critical iterate. -/
theorem map_criticalOrbit {K L : Type*} [Field K] [Field L]
    (φ : K →+* L) (d : ℕ) (c : K) (n : ℕ) :
    φ (criticalOrbit d c n) = criticalOrbit d (φ c) n := by
  induction n with
  | zero => simp only [criticalOrbit_zero, map_zero]
  | succ n ih => simp only [criticalOrbit_succ, map_add, map_pow, ih]

/-- Embeddings preserve the exact equality pattern, hence every critical orbit type. -/
theorem criticalOrbit_embedding_eq_iff {K L : Type*} [Field K] [Field L]
    (φ : K →+* L) (d : ℕ) (c : K) (m n : ℕ) :
    criticalOrbit d (φ c) m = criticalOrbit d (φ c) n ↔
      criticalOrbit d c m = criticalOrbit d c n := by
  rw [← map_criticalOrbit, ← map_criticalOrbit, φ.injective.eq_iff]

/-- In the cubic family, the boundary modulus `√2` already forces escape. -/
theorem cubic_criticalOrbit_unbounded_or_strict (c : ℂ) :
    ¬ IsBounded (range (criticalOrbit 1 c)) ∨ ‖c‖ < Real.sqrt 2 := by
  by_cases hb : IsBounded (range (criticalOrbit 1 c))
  · right
    have h := (bounded_criticalOrbit_iff 1 c).mp hb
    have h1 := h 1
    simp only [criticalOrbit_one, show 1 + 1 = 2 from rfl] at h1
    have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hs0 := Real.sqrt_nonneg (2 : ℝ)
    by_contra hlt
    have hc : ‖c‖ ^ 2 = 2 := by nlinarith only [h1, hs, hs0, not_lt.mp hlt]
    have h2 := h 2
    simp only [criticalOrbit_succ, criticalOrbit_zero, zero_pow (by norm_num : 1 + 2 ≠ 0),
      zero_add] at h2
    change ‖c ^ 3 + c‖ ^ 2 ≤ 2 at h2
    rw [show c ^ 3 + c = c * (c ^ 2 + 1) by ring, norm_mul, mul_pow, hc] at h2
    have hw : ‖c ^ 2‖ ^ 2 = 4 := by rw [norm_pow, hc]; norm_num
    have hw' : (c ^ 2).re * (c ^ 2).re + (c ^ 2).im * (c ^ 2).im = 4 := by
      simpa only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] using hw
    have hplus : 2 * (((c ^ 2).re + 1) ^ 2 + (c ^ 2).im ^ 2) ≤ 2 := by
      simpa only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
        Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
        add_zero, ← pow_two] using h2
    have hre : (c ^ 2).re = -2 := by
      nlinarith only [hw', hplus, sq_nonneg ((c ^ 2).re + 2), sq_nonneg (c ^ 2).im]
    have him : (c ^ 2).im = 0 := by
      have hz : (c ^ 2).im ^ 2 = 0 := by nlinarith only [hw', hre]
      exact sq_eq_zero_iff.mp hz
    have hcsq : c ^ 2 = -2 := by
      apply Complex.ext
      · simpa using hre
      · simpa using him
    have he2 : criticalOrbit 1 c 2 = -c := by
      simp only [criticalOrbit_succ, criticalOrbit_zero,
        zero_pow (by norm_num : 1 + 2 ≠ 0), zero_add]
      change c ^ 3 + c = -c
      calc
        c ^ 3 + c = c * c ^ 2 + c := by ring
        _ = -c := by rw [hcsq]; ring
    have he3 : criticalOrbit 1 c 3 = 3 * c := by
      rw [criticalOrbit_succ, he2]
      change (-c) ^ 3 + c = 3 * c
      calc
        (-c) ^ 3 + c = -c * c ^ 2 + c := by ring
        _ = 3 * c := by rw [hcsq]; ring
    have h3 := h 3
    rw [he3, norm_mul, mul_pow] at h3
    norm_num [hc] at h3
  · exact Or.inl hb

end Bottcher.Arithmetic

