import GaloisForLFunctions.RHTower.EulerDeletionNestedProjectionCovariance

/-!
# Canonical clock resolvents for Euler-deletion layers

At every actual chronological cutoff, the literal paired Möbius quotient has a
finite beta-resolvent indexed by the quotient of the two physical clocks. A
drift layer is therefore a difference of two such complete signed resolvents,
with only its local innovation removed.
-/

noncomputable section

open Finset

namespace RHTower.DeletionResidueMartingale

/-- A globally positive ratio representation for a source quotient. At genuine history cutoffs
it reduces to the actual quotient of the two clocks. -/
def canonicalClockRatio (N L : ℕ) : ℕ := max 1 (clock N / clock L)

/-- Canonical beta resolvent of the literal paired source on a physical fibre. -/
def canonicalBetaResolvent (N L r : ℕ) : ℝ :=
  (∫ x in (0 : ℝ)..1, (1 - x) * x ^ r *
    ∑ s ∈ range (canonicalClockRatio N L),
      (x ^ (s * clock L) * pairedMoebiusSource N (r + s * clock L)) *
        (1 - x ^ (canonicalClockRatio N L * clock L))⁻¹) /
    cellMeasure.real (historyFibre L r)

/-- At an actual history cutoff, the canonical ratio is precisely the quotient of its clocks. -/
theorem canonicalClockRatio_eq_div_of_le (N L : ℕ) (hLN : L ≤ N) :
    canonicalClockRatio N L = clock N / clock L := by
  unfold canonicalClockRatio
  apply max_eq_right
  exact Nat.one_le_iff_ne_zero.mpr
    (Nat.div_pos (Nat.le_of_dvd (clock_pos N) (clock_dvd hLN)) (clock_pos L)).ne'

/-- At every actual history cutoff, the canonical resolvent is the literal paired quotient. -/
theorem pairedMoebiusQuotient_eq_canonicalBetaResolvent_of_le
    (N L r : ℕ) (hLN : L ≤ N) (hr : r < clock L) :
    pairedMoebiusQuotient N L r = canonicalBetaResolvent N L r := by
  rw [canonicalBetaResolvent, canonicalClockRatio_eq_div_of_le N L hLN]
  have hKpos : 0 < clock N / clock L :=
    Nat.div_pos (Nat.le_of_dvd (clock_pos N) (clock_dvd hLN)) (clock_pos L)
  letI : NeZero (clock N / clock L) := ⟨hKpos.ne'⟩
  rw [pairedMoebiusQuotient_eq_beta_periodic_geometric N L r (clock N / clock L) hr
    (Nat.div_mul_cancel (clock_dvd hLN)) hKpos]
  apply congrArg (fun y : ℝ => y / cellMeasure.real (historyFibre L r))
  apply intervalIntegral.integral_congr
  intro x hx
  change (1 - x) * x ^ r *
      (∑ s : ZMod (clock N / clock L),
        (x ^ (s.val * clock L) * pairedMoebiusSource N (r + s.val * clock L)) *
          (1 - x ^ ((clock N / clock L) * clock L))⁻¹) =
      (1 - x) * x ^ r *
        ∑ s ∈ range (clock N / clock L),
          (x ^ (s * clock L) * pairedMoebiusSource N (r + s * clock L)) *
            (1 - x ^ ((clock N / clock L) * clock L))⁻¹
  congr 1
  rw [sum_zmod_eq_sum_range_natCast]
  apply Finset.sum_congr rfl
  intro s hs
  rw [ZMod.val_cast_of_lt (Finset.mem_range.mp hs)]

/-- On every genuine chronological step, a drift-layer coordinate is the difference of the
two canonical beta resolvents of its complete paired source, followed only by its local
innovation. The two source numerators retain every Möbius sign simultaneously. -/
theorem historyLayer_predictableDrift_apply_eq_canonicalBetaResolvent_sub_innovation
    (l N j : ℕ) (hlN : l < N) :
    (historyLayer l (predictableDrift N)) j =
      canonicalBetaResolvent N (l + 1) (j % clock (l + 1)) -
        canonicalBetaResolvent N l (j % clock l) - signedInnovation l j := by
  rw [historyLayer_predictableDrift_apply_eq_pairedMoebiusQuotient_sub_innovation,
    if_pos hlN,
    pairedMoebiusQuotient_eq_canonicalBetaResolvent_of_le N (l + 1)
      (j % clock (l + 1)) (Nat.succ_le_of_lt hlN) (Nat.mod_lt _ (clock_pos _)),
    pairedMoebiusQuotient_eq_canonicalBetaResolvent_of_le N l (j % clock l)
      (Nat.le_of_lt hlN) (Nat.mod_lt _ (clock_pos _))]

end RHTower.DeletionResidueMartingale
