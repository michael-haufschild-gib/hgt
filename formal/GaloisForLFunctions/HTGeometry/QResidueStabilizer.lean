import GaloisForLFunctions.HTGeometry.QResidueSpectrum

/-!
# The summability stabilizer meets only finitely many orbits

Scaling multiplies the `q`-discrete residue at an orbit by a nonzero factor and moves the orbit, so
the stabilizer of the summability class permutes the residue support.  The residue support lies in
the `q`-orbits of the finitely many poles, so the stabilizer is contained in finitely many orbits:
its quotient by `q^ℤ` is finite.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

open scoped RatFunc

noncomputable section

variable {K : Type*} [Field K]

theorem qOrbitResidue_ratFuncScale {q : K} {a : K} (ha : a ≠ 0) (α : K) (d : ℕ)
    (r : RatFunc K) :
    qOrbitResidue q α d (ratFuncScale a ha r)
      = a ^ (-(d : ℤ)) * qOrbitResidue q (a * α) d r := by
  rw [qOrbitResidue, qOrbitResidue, mul_finsum]
  refine finsum_congr fun n => ?_
  rw [polePart_ratFuncScale, multOrbit, multOrbit]
  rw [show a * (α * q ^ n) = a * α * q ^ n from by ring]
  ring

/-- The residue support: the nonzero points carrying a nonvanishing `q`-discrete residue. -/
def residueSupport (q : K) (r : RatFunc K) : Set K :=
  {α : K | α ≠ 0 ∧ ∃ d : ℕ, 0 < d ∧ qOrbitResidue q α d r ≠ 0}

theorem qOrbitResidue_eq_of_qSummable {q : K} (hq : q ≠ 0) (hqtor : ∀ n : ℤ, n ≠ 0 → q ^ n ≠ 1)
    {a : K} (ha : a ≠ 0) (r : RatFunc K) (hsum : QSummable q hq (ratFuncScale a ha r - r))
    {α : K} (hα : α ≠ 0) {d : ℕ} (hd : 0 < d) :
    qOrbitResidue q α d (ratFuncScale a ha r) = qOrbitResidue q α d r := by
  obtain ⟨k, hk⟩ := hsum
  have hzero : qOrbitResidue q α d (ratFuncScale a ha r - r) = 0 := by
    rw [hk]
    exact qOrbitResidue_ratFuncScale_sub hq hα hqtor hd k
  have hsplit : qOrbitResidue q α d (ratFuncScale a ha r - r)
      = qOrbitResidue q α d (ratFuncScale a ha r) - qOrbitResidue q α d r := by
    rw [show ratFuncScale a ha r - r = ratFuncScale a ha r + -r from by ring,
      qOrbitResidue_add hq hα hqtor hd]
    have hneg : qOrbitResidue q α d (-r) = -qOrbitResidue q α d r := by
      rw [show (-r : RatFunc K) = algebraMap K (RatFunc K) (-1) * r from by
        rw [map_neg, map_one]; ring, qOrbitResidue_smul hq hα hqtor hd]
      ring
    rw [hneg]
    ring
  rw [hsplit] at hzero
  exact sub_eq_zero.1 hzero

/-- **The stabilizer permutes the residue support.** -/
theorem mul_mem_residueSupport {q : K} (hq : q ≠ 0) (hqtor : ∀ n : ℤ, n ≠ 0 → q ^ n ≠ 1)
    {a : K} (ha : a ≠ 0) (r : RatFunc K) (hsum : QSummable q hq (ratFuncScale a ha r - r))
    {α : K} (hα : α ∈ residueSupport q r) : a * α ∈ residueSupport q r := by
  obtain ⟨hα0, d, hd, hres⟩ := hα
  refine ⟨mul_ne_zero ha hα0, d, hd, ?_⟩
  have heq := qOrbitResidue_eq_of_qSummable hq hqtor ha r hsum hα0 hd
  rw [qOrbitResidue_ratFuncScale ha α d r] at heq
  intro h0
  rw [h0, mul_zero] at heq
  exact hres heq.symm

/-- The residue support lies in the `q`-orbits of the poles. -/
theorem residueSupport_subset_orbit_poles {q : K} (r : RatFunc K) {α : K}
    (hα : α ∈ residueSupport q r) :
    ∃ n : ℤ, r.denom.IsRoot (α * q ^ n) := by
  obtain ⟨hα0, d, hd, hres⟩ := hα
  by_contra hcon
  push Not at hcon
  refine hres ?_
  rw [qOrbitResidue_eq_sum r (∅ : Finset ℤ) ?_, Finset.sum_empty]
  intro n hn
  refine absurd ?_ hn
  refine polePart_eq_zero_of_poleOrder_zero hd ?_
  by_contra hpole
  exact hcon n ((poleOrder_ne_zero_iff r _).1 hpole)

/-- **The summability stabilizer meets only finitely many orbits.**  Every element of the
stabilizer is a pole divided by a fixed residue-support point, times a power of `q`. -/
theorem qSummableStabilizer_eq_pole_div {q : K} (hq : q ≠ 0)
    (hqtor : ∀ n : ℤ, n ≠ 0 → q ^ n ≠ 1) (r : RatFunc K)
    {α₀ : K} (hα₀ : α₀ ∈ residueSupport q r)
    {a : K} (ha : a ≠ 0) (hsum : QSummable q hq (ratFuncScale a ha r - r)) :
    ∃ β : K, r.denom.IsRoot β ∧ ∃ n : ℤ, a = β * q ^ (-n) / α₀ := by
  obtain ⟨n, hn⟩ := residueSupport_subset_orbit_poles r
    (mul_mem_residueSupport hq hqtor ha r hsum hα₀)
  refine ⟨a * α₀ * q ^ n, hn, n, ?_⟩
  have hα₀0 : α₀ ≠ 0 := hα₀.1
  have hqn : (q : K) ^ n ≠ 0 := zpow_ne_zero n hq
  rw [zpow_neg]
  field_simp


theorem qOrbitResidue_sub {q : K} (hq : q ≠ 0) (hqtor : ∀ n : ℤ, n ≠ 0 → q ^ n ≠ 1)
    {α : K} (hα : α ≠ 0) {d : ℕ} (hd : 0 < d) (s t : RatFunc K) :
    qOrbitResidue q α d (s - t) = qOrbitResidue q α d s - qOrbitResidue q α d t := by
  rw [show s - t = s + -t from by ring, qOrbitResidue_add hq hα hqtor hd]
  have hneg : qOrbitResidue q α d (-t) = -qOrbitResidue q α d t := by
    rw [show (-t : RatFunc K) = algebraMap K (RatFunc K) (-1) * t from by
      rw [map_neg, map_one]; ring, qOrbitResidue_smul hq hα hqtor hd]
    ring
  rw [hneg]
  ring

end

end GaloisForLFunctions.HTGeometry
