import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheGhostRingOfTheArithmeticSquare

/-!
# The archimedean fibre of the arithmetic square

The arithmetic square `𝒢` sits in the ring of sequences on the degrees `n ≥ 1`, on which the
Frobenius `F_k` is the shift `(F_k y)_n = y_{kn}` (`shift`). The same shift acts on real sequences,
and its eigenvectors are the **weight lines** `χ_z = (n^z)_n`: `F_k χ_z = k^z χ_z` (`shift_weight`).

* **The jets.** `τ = χ_{−2} = (n^{−2})_n` generates the ring of even germs at the fixed point of the
  dilation of `ℝ`. `F_k τ^j = k^{−2j} τ^j` (`shift_tau_pow`), and the trace of `F_n` on the jets is
  `Σ_j n^{−2j} = 1 + 1/(n² − 1)` (`hasSum_trace_shift_jets`): the archimedean part of the point
  count of `Spec ℤ`.
* **Transposition.** On a weight line the relation `F_k V_k = k` forces `V_k = k^{1−z}`
  (`eq_rpow_of_shift_smul_weight`): the transpose of weight `z` is weight `1 − z`, the functional
  equation. On the jets `V_k τ^j = k^{1+2j} τ^j`, and the trace of `V_m F_n`, `m < n`, is
  `Σ_j m^{1+2j} n^{−2j} = m/(1 − (m/n)²)` (`hasSum_trace_verschiebung_shift_jets`): the archimedean
  part of Weil's off-diagonal. On the weights `0` and `1` it is `m + n`, the pole plane.
* **Support.** The Witt Verschiebung satisfies the projection formula
  `V_k(x · F_k y) = V_k(x) · y` (`verschiebungFun_mul_frobeniusFun`). Any map with this property
  vanishes off the multiples of `k` (`eq_zero_of_projection_formula`), because
  `V(y)(e_k − k) = 0`. So a Witt Verschiebung returns `0` at every pair of degrees neither of which
  divides the other, where the jets do not vanish; and the Verschiebung of the jets has `V_k 1 = k`,
  not the orbit `e_k` (`orbitSeq_ne_const`). The archimedean fibre shares the Frobenius of the
  square and not its Verschiebung.
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-- The Frobenius `F_k` on real sequences: `(F_k y)_n = y_{kn}`. -/
def shift (k : ℕ+) : (ℕ+ → ℝ) →+* (ℕ+ → ℝ) where
  toFun y := fun n => y (k * n)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem shift_apply (k : ℕ+) (y : ℕ+ → ℝ) (n : ℕ+) : shift k y n = y (k * n) := rfl

theorem shift_smul (k : ℕ+) (a : ℝ) (y : ℕ+ → ℝ) : shift k (a • y) = a • shift k y := rfl

/-- On integer sequences the shift is the Frobenius of the arithmetic square. -/
theorem shift_intCast (k : ℕ+) (x : ℕ+ → ℤ) :
    shift k (fun n => (x n : ℝ)) = fun n => (frobeniusFun k x n : ℝ) := rfl

/-! ### Weight lines -/

/-- The weight line `χ_z = (n^z)_n`. -/
def weight (z : ℝ) : ℕ+ → ℝ := fun n => ((n : ℕ) : ℝ) ^ z

/-- **`F_k` acts on the weight `z` by `k^z`.** -/
theorem shift_weight (k : ℕ+) (z : ℝ) : shift k (weight z) = (((k : ℕ) : ℝ) ^ z) • weight z := by
  funext n
  simp only [shift_apply, weight, PNat.mul_coe, Nat.cast_mul, Pi.smul_apply, smul_eq_mul]
  exact Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- **Transposition is `z ↦ 1 − z`.** On a weight line, `F_k V = k` forces `V = k^{1−z}`. -/
theorem eq_rpow_of_shift_smul_weight {k : ℕ+} {z a : ℝ}
    (h : shift k (a • weight z) = (((k : ℕ) : ℝ)) • weight z) : a = ((k : ℕ) : ℝ) ^ (1 - z) := by
  have hk : (0 : ℝ) < ((k : ℕ) : ℝ) := by exact_mod_cast k.pos
  have h1 := congrFun h 1
  simp only [shift_apply, Pi.smul_apply, weight, smul_eq_mul, mul_one, PNat.one_coe, Nat.cast_one,
    Real.one_rpow] at h1
  rw [Real.rpow_sub hk, Real.rpow_one, eq_div_iff (Real.rpow_pos_of_pos hk z).ne']
  exact h1

/-- The transpose exists: `F_k (k^{1−z} χ_z) = k χ_z`. -/
theorem shift_rpow_smul_weight (k : ℕ+) (z : ℝ) :
    shift k ((((k : ℕ) : ℝ) ^ (1 - z)) • weight z) = (((k : ℕ) : ℝ)) • weight z := by
  have hk : (0 : ℝ) < ((k : ℕ) : ℝ) := by exact_mod_cast k.pos
  rw [shift_smul, shift_weight, smul_smul, ← Real.rpow_add hk, sub_add_cancel, Real.rpow_one]

/-- **The pole plane.** On the weights `0` and `1` the trace of `V_m F_n` is `m + n`. -/
theorem trace_polePlane (m n : ℕ+) :
    ((m : ℕ) : ℝ) ^ (1 - (0 : ℝ)) * ((n : ℕ) : ℝ) ^ (0 : ℝ) +
      ((m : ℕ) : ℝ) ^ (1 - (1 : ℝ)) * ((n : ℕ) : ℝ) ^ (1 : ℝ) = (m : ℕ) + (n : ℕ) := by
  simp

/-! ### The jets -/

/-- The jet coordinate `τ = (n^{−2})_n`. -/
def tau : ℕ+ → ℝ := fun n => ((((n : ℕ) : ℝ)) ^ 2)⁻¹

/-- `τ` is the weight line `−2`. -/
theorem tau_eq_weight : tau = weight (-2) := by
  funext n
  rw [tau, weight, Real.rpow_neg (Nat.cast_nonneg _)]
  norm_num

/-- `F_k τ = k^{−2} τ`. -/
theorem shift_tau (k : ℕ+) : shift k tau = ((((k : ℕ) : ℝ)) ^ 2)⁻¹ • tau := by
  funext n
  simp only [shift_apply, tau, PNat.mul_coe, Nat.cast_mul, Pi.smul_apply, smul_eq_mul]
  rw [mul_pow, mul_inv]

/-- **`F_k` acts on the `j`-th jet by `k^{−2j}`.** -/
theorem shift_tau_pow (k : ℕ+) (j : ℕ) :
    shift k (tau ^ j) = (((((k : ℕ) : ℝ)) ^ 2)⁻¹ ^ j) • tau ^ j := by
  rw [map_pow, shift_tau, smul_pow]

/-- **The archimedean Lefschetz number.** The trace of `F_n` on the jets is
`Σ_j n^{−2j} = 1 + 1/(n² − 1)`. -/
theorem hasSum_trace_shift_jets {n : ℕ+} (hn : 1 < n) :
    HasSum (fun j : ℕ => ((((n : ℕ) : ℝ)) ^ 2)⁻¹ ^ j) (1 + 1 / ((((n : ℕ) : ℝ)) ^ 2 - 1)) := by
  have hn2 : (2 : ℝ) ≤ ((n : ℕ) : ℝ) := by exact_mod_cast hn
  have hsq : (1 : ℝ) < ((n : ℕ) : ℝ) ^ 2 := by nlinarith
  have h := hasSum_geometric_of_lt_one (r := ((((n : ℕ) : ℝ)) ^ 2)⁻¹) (by positivity)
    (inv_lt_one_of_one_lt₀ hsq)
  convert h using 1
  have h1 : ((n : ℕ) : ℝ) ^ 2 - 1 ≠ 0 := by linarith
  have h2 : ((n : ℕ) : ℝ) ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- The transpose on the jets: `F_k (k^{1+2j} τ^j) = k τ^j`. -/
theorem shift_smul_tau_pow (k : ℕ+) (j : ℕ) :
    shift k ((((k : ℕ) : ℝ) * (((k : ℕ) : ℝ) ^ 2) ^ j) • tau ^ j) = (((k : ℕ) : ℝ)) • tau ^ j := by
  have hk : ((k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast k.ne_zero
  rw [shift_smul, shift_tau_pow, smul_smul, inv_pow, mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero _ (pow_ne_zero _ hk)), mul_one]

/-- **The archimedean intersection number.** For `m < n` the trace of `V_m F_n` on the jets is
`Σ_j m^{1+2j} n^{−2j} = m/(1 − (m/n)²)`. -/
theorem hasSum_trace_verschiebung_shift_jets {m n : ℕ+} (h : m < n) :
    HasSum (fun j : ℕ => (((m : ℕ) : ℝ) * (((m : ℕ) : ℝ) ^ 2) ^ j) * ((((n : ℕ) : ℝ)) ^ 2)⁻¹ ^ j)
      (((m : ℕ) : ℝ) / (1 - (((m : ℕ) : ℝ) / ((n : ℕ) : ℝ)) ^ 2)) := by
  have hm : (0 : ℝ) < ((m : ℕ) : ℝ) := by exact_mod_cast m.pos
  have hn : (0 : ℝ) < ((n : ℕ) : ℝ) := by exact_mod_cast n.pos
  have hmn : ((m : ℕ) : ℝ) < ((n : ℕ) : ℝ) := by exact_mod_cast h
  have hr0 : (0 : ℝ) ≤ (((m : ℕ) : ℝ) / ((n : ℕ) : ℝ)) ^ 2 := by positivity
  have hr1 : (((m : ℕ) : ℝ) / ((n : ℕ) : ℝ)) ^ 2 < 1 := by
    have : ((m : ℕ) : ℝ) / ((n : ℕ) : ℝ) < 1 := (div_lt_one hn).mpr hmn
    have h0 : (0 : ℝ) ≤ ((m : ℕ) : ℝ) / ((n : ℕ) : ℝ) := by positivity
    nlinarith
  have hs := (hasSum_geometric_of_lt_one hr0 hr1).mul_left ((m : ℕ) : ℝ)
  rw [← div_eq_mul_inv] at hs
  have hterm : (fun j : ℕ => (((m : ℕ) : ℝ) * (((m : ℕ) : ℝ) ^ 2) ^ j) *
      ((((n : ℕ) : ℝ)) ^ 2)⁻¹ ^ j) =
      fun j : ℕ => ((m : ℕ) : ℝ) * ((((m : ℕ) : ℝ) / ((n : ℕ) : ℝ)) ^ 2) ^ j := by
    funext j
    rw [div_pow, div_pow, inv_pow, mul_assoc, ← div_eq_mul_inv]
  rw [hterm]
  exact hs

/-! ### The Witt Verschiebung is supported on multiples -/

/-- **The projection formula** for the Witt Verschiebung: `V_k(x · F_k y) = V_k(x) · y`. -/
theorem verschiebungFun_mul_frobeniusFun (k : ℕ+) (x y : ℕ+ → ℤ) :
    verschiebungFun k (x * frobeniusFun k y) = verschiebungFun k x * y := by
  funext n
  by_cases h : (k : ℕ) ∣ n
  · obtain ⟨n', rfl⟩ := PNat.dvd_iff.mpr h
    rw [Pi.mul_apply, verschiebungFun_mul, verschiebungFun_mul, Pi.mul_apply, frobeniusFun_apply,
      mul_assoc]
  · rw [Pi.mul_apply, verschiebungFun_of_not_dvd _ _ h, verschiebungFun_of_not_dvd _ _ h, zero_mul]

/-- The orbit `e_k` as a real sequence. -/
def orbitSeq (k : ℕ+) : ℕ+ → ℝ := fun n => if (k : ℕ) ∣ n then ((k : ℕ) : ℝ) else 0

theorem orbitSeq_eq_orbit (k n : ℕ+) : orbitSeq k n = ((orbit k).1 n : ℝ) := by
  rw [orbit_apply, orbitSeq]
  split_ifs <;> simp

/-- `F_k e_k = k`. -/
theorem shift_orbitSeq (k : ℕ+) : shift k (orbitSeq k) = fun _ => ((k : ℕ) : ℝ) := by
  funext n
  rw [shift_apply, orbitSeq, if_pos (by rw [PNat.mul_coe]; exact dvd_mul_right _ _)]

/-- **A Verschiebung with the projection formula is supported on the multiples of `k`.** From
`F_k e_k = k`: `k V(y) = V(y · F_k e_k) = V(y) e_k`, and `e_k` vanishes off the multiples. -/
theorem eq_zero_of_projection_formula (k : ℕ+) (V : (ℕ+ → ℝ) → (ℕ+ → ℝ)) (y : ℕ+ → ℝ)
    (hsmul : V ((((k : ℕ) : ℝ)) • y) = (((k : ℕ) : ℝ)) • V y)
    (hproj : V (y * shift k (orbitSeq k)) = V y * orbitSeq k) {n : ℕ+} (hn : ¬ (k : ℕ) ∣ n) :
    V y n = 0 := by
  have hk : ((k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast k.ne_zero
  have hy : y * shift k (orbitSeq k) = (((k : ℕ) : ℝ)) • y := by
    rw [shift_orbitSeq]
    funext i
    simp [mul_comm]
  rw [hy, hsmul] at hproj
  have h := congrFun hproj n
  simp only [Pi.smul_apply, Pi.mul_apply, orbitSeq, if_neg hn, mul_zero, smul_eq_mul] at h
  exact (mul_eq_zero.mp h).resolve_left hk

/-- The Verschiebung of the jets sends `1` to the constant `k`, the Witt Verschiebung to the orbit
`e_k`; for `k ≥ 2` they differ. -/
theorem orbitSeq_ne_const {k : ℕ+} (hk : 1 < k) : orbitSeq k ≠ fun _ => ((k : ℕ) : ℝ) := by
  intro h
  have h1 := congrFun h 1
  have hnd : ¬ (k : ℕ) ∣ ((1 : ℕ+) : ℕ) := by
    rw [PNat.one_coe, Nat.dvd_one]
    exact fun h1 => hk.ne' (PNat.eq (by simpa using h1))
  rw [orbitSeq, if_neg hnd] at h1
  exact (by exact_mod_cast k.ne_zero : ((k : ℕ) : ℝ) ≠ 0) h1.symm

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
