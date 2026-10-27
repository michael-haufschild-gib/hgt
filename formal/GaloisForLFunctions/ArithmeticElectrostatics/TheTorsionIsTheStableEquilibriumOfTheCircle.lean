import GaloisForLFunctions.HTGeometry.ContinuousKernelFredholmDeterminant
import GaloisForLFunctions.ArithmeticEffectivityTheory.TheLogEnergyOfRootsOfUnity

/-!
# The torsion is the stable equilibrium of the circle

On the zero divisor equilibrium is computed and stability is the open sign. On the characteristic
circle both are theorems, and the torsion realizes them.

* **Fekete's bound** (`sum_sum_log_norm_sub_le`): for `N` distinct points of the unit circle,
  `Σ_{i ≠ j} log |z_i − z_j| ≤ N log N`. The product of the distances is the squared Vandermonde
  determinant, and Hadamard's inequality bounds a determinant with unimodular entries by `N^{N/2}`.
  In electrostatic terms: the discrete logarithmic energy `−Σ_{i ≠ j} log |z_i − z_j|` of `N` unit
  charges on the circle is at least `−N log N`.
* **Attained by the torsion** (`logEnergy_self_eq`): the `N`-th roots of unity — the union of the
  torsion orbits `O_d`, `d ∣ N` — have energy exactly `N log N` (the log-discriminant of `X^N − 1`).

So the torsion of order `N` is a minimal-energy configuration of `N` charges on the circle: its
equilibrium is stable, with the self-energy `N log N` computed by an integer (`N^N`). This is the
positivity the circle supplies for free — the base of the circle's intersection theory — and the
standard against which the divisor's missing stability is measured.
-/

open Finset Matrix

namespace GaloisForLFunctions.ArithmeticElectrostatics

/-- Ordered pairs of distinct indices: a symmetric summand vanishing on the diagonal sums to twice
its strictly increasing part. -/
theorem sum_sum_eq_two_mul_sum_Ioi {N : ℕ} (f : Fin N → Fin N → ℝ) (hsymm : ∀ i j, f i j = f j i)
    (hdiag : ∀ i, f i i = 0) :
    ∑ i, ∑ j, f i j = 2 * ∑ i, ∑ j ∈ Ioi i, f i j := by
  have hsplit : ∀ i j, f i j = (if i < j then f i j else 0) + (if j < i then f i j else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | rfl | h
    · rw [if_pos h, if_neg (lt_asymm h), add_zero]
    · simp [hdiag]
    · rw [if_neg (lt_asymm h), if_pos h, zero_add]
  have hlow : ∑ i, ∑ j, (if j < i then f i j else 0) = ∑ i, ∑ j, (if i < j then f i j else 0) := by
    rw [sum_comm]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by rw [hsymm]
  have hIoi : ∀ i, ∑ j, (if i < j then f i j else 0) = ∑ j ∈ Ioi i, f i j := fun i => by
    rw [← sum_filter, filter_lt_eq_Ioi]
  calc ∑ i, ∑ j, f i j
      = ∑ i, ∑ j, ((if i < j then f i j else 0) + (if j < i then f i j else 0)) :=
        sum_congr rfl fun i _ => sum_congr rfl fun j _ => hsplit i j
    _ = ∑ i, ∑ j, (if i < j then f i j else 0) + ∑ i, ∑ j, (if j < i then f i j else 0) := by
        rw [← sum_add_distrib]; exact sum_congr rfl fun i _ => sum_add_distrib
    _ = 2 * ∑ i, ∑ j, (if i < j then f i j else 0) := by rw [hlow, ← two_mul]
    _ = 2 * ∑ i, ∑ j ∈ Ioi i, f i j := by rw [sum_congr rfl fun i _ => hIoi i]

/-- **Fekete's bound on the circle.** `N` distinct points of the unit circle satisfy
`Σ_{i ≠ j} log |z_i − z_j| ≤ N log N` (the diagonal contributes `log 0 = 0`). -/
theorem sum_sum_log_norm_sub_le {N : ℕ} (z : Fin N → ℂ) (hz : ∀ i, ‖z i‖ = 1)
    (hinj : Function.Injective z) :
    ∑ i, ∑ j, Real.log ‖z i - z j‖ ≤ N * Real.log N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  -- Hadamard: a determinant with unimodular entries has modulus at most `N^{N/2}`
  have hentry : ∀ i j, ‖vandermonde z i j‖ ≤ 1 := fun i j => by
    rw [vandermonde_apply, norm_pow, hz, one_pow]
  have hhad := ContinuousKernelFredholm.complex_hadamard_entry_bound (vandermonde z) hentry
  rw [mul_one] at hhad
  have hdet0 : (vandermonde z).det ≠ 0 := det_vandermonde_ne_zero_iff.mpr hinj
  -- the logarithm of the Vandermonde product is the increasing pair sum
  have hfac : ∀ i, ∀ j ∈ Ioi i, ‖z j - z i‖ ≠ 0 := fun i j hj =>
    norm_ne_zero_iff.mpr (sub_ne_zero.mpr fun h => (ne_of_gt (mem_Ioi.mp hj)) (hinj h))
  have hlogdet : Real.log ‖(vandermonde z).det‖ = ∑ i, ∑ j ∈ Ioi i, Real.log ‖z j - z i‖ := by
    rw [det_vandermonde, norm_prod, Real.log_prod fun i _ => by
      rw [norm_prod]; exact prod_ne_zero_iff.mpr (hfac i)]
    exact sum_congr rfl fun i _ => by rw [norm_prod, Real.log_prod (hfac i)]
  have hbound : Real.log ‖(vandermonde z).det‖ ≤ N * (Real.log N / 2) := by
    calc Real.log ‖(vandermonde z).det‖ ≤ Real.log (Real.sqrt N ^ N) :=
          Real.log_le_log (norm_pos_iff.mpr hdet0) hhad
      _ = N * (Real.log N / 2) := by rw [Real.log_pow, Real.log_sqrt (Nat.cast_nonneg N)]
  rw [sum_sum_eq_two_mul_sum_Ioi (fun i j => Real.log ‖z i - z j‖)
    (fun i j => by rw [norm_sub_rev]) (fun i => by simp)]
  have hrev : ∑ i, ∑ j ∈ Ioi i, Real.log ‖z i - z j‖ = ∑ i, ∑ j ∈ Ioi i, Real.log ‖z j - z i‖ :=
    sum_congr rfl fun i _ => sum_congr rfl fun j _ => by rw [norm_sub_rev]
  rw [hrev, ← hlogdet]
  linarith

/-- **The torsion attains Fekete's bound**: the `N`-th roots of unity have
`Σ_{ζ, η} log |ζ − η| = N log N`. -/
theorem logEnergy_self_eq {N : ℕ} (hN : 0 < N) :
    ArithmeticEffectivityTheory.logEnergy N N = N * Real.log N := by
  rw [ArithmeticEffectivityTheory.logEnergy_eq hN hN, Nat.gcd_self, Nat.lcm_self]

end GaloisForLFunctions.ArithmeticElectrostatics
