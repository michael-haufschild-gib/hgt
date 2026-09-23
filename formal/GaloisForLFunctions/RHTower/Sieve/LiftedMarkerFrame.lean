import GaloisForLFunctions.RHTower.Sieve.LiftedMarkerBlock

/-!
# The parameters of a lifted marker block

The cofactor scale is a perfect square, so its square root is an integer and every start in
`[√y/2, √y]` is realised exactly.  The marker scale is that square root times a lift factor `W`, the
physical scale is the product of the two, and the physical window is twice the cell length times the
marker scale.  With these choices the reciprocal start of a marker of the block lands in
`[u, 2u)` — exactly the realisable range — and the marker's cell is between one and two fibres long.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- The cofactor scale: a perfect square, so its square root is exact. -/
def liftScale (u : ℕ) : ℝ := ((2 * u : ℕ) : ℝ) ^ (2 : ℕ)

theorem sqrt_liftScale (u : ℕ) : Real.sqrt (liftScale u) = ((2 * u : ℕ) : ℝ) := by
  rw [liftScale, Real.sqrt_sq (by positivity)]

theorem liftScale_eq (u : ℕ) : liftScale u = 4 * (u : ℝ) ^ (2 : ℕ) := by
  rw [liftScale]
  push_cast
  ring

/-- The lift factor. -/
def liftFactor (u : ℕ) : ℕ := ⌊Real.log (liftScale u)⌋₊

/-- The marker scale, lifted by `liftFactor`. -/
def liftMarkerScale (u : ℕ) : ℕ := 2 * u * liftFactor u

/-- The physical scale. -/
def liftPhysScale (u : ℕ) : ℕ := 2 * u * liftMarkerScale u

/-- The cell-length parameter, one more than the ceiling of the cofactor window. -/
def liftCellLen (β : ℝ) (u : ℕ) : ℕ := ⌈cardLength β (liftScale u)⌉₊ + 1

/-- The physical window. -/
def liftWindow (β : ℝ) (u : ℕ) : ℕ := 2 * liftCellLen β u * liftMarkerScale u

/-! ## The reciprocal starts of the block -/

/-- **Every marker of the block has a start above `u`.** -/
theorem liftStart_ge {u p : ℕ} (hp : 0 < p) (hple : p ≤ 2 * liftMarkerScale u) :
    u ≤ liftPhysScale u / p := by
  have hM : 0 < liftMarkerScale u := by omega
  have h1 : liftPhysScale u / (2 * liftMarkerScale u) ≤ liftPhysScale u / p :=
    Nat.div_le_div_left hple hp
  have h2 : liftPhysScale u / (2 * liftMarkerScale u) = u := by
    rw [liftPhysScale, show 2 * u * liftMarkerScale u = u * (2 * liftMarkerScale u) by ring]
    exact Nat.mul_div_cancel _ (by omega)
  omega

/-- **Every marker of the block has a start below `2u`.** -/
theorem liftStart_lt {u p : ℕ} (hu : 0 < u) (hp : liftMarkerScale u < p) :
    liftPhysScale u / p < 2 * u := by
  have hp0 : 0 < p := by omega
  refine (Nat.div_lt_iff_lt_mul hp0).2 ?_
  rw [liftPhysScale]
  exact mul_lt_mul_of_pos_left hp (by omega : 0 < 2 * u)

/-- **The physical window fits inside the square of the marker scale.** -/
theorem liftPhys_add_window_le {β : ℝ} {u : ℕ}
    (hL : u + liftCellLen β u ≤ u * liftFactor u) :
    liftPhysScale u + liftWindow β u ≤ liftMarkerScale u * liftMarkerScale u := by
  rw [liftPhysScale, liftWindow, liftMarkerScale]
  have hstep : 2 * u + 2 * liftCellLen β u ≤ 2 * (u * liftFactor u) := by omega
  calc 2 * u * (2 * u * liftFactor u) + 2 * liftCellLen β u * (2 * u * liftFactor u)
      = (2 * u + 2 * liftCellLen β u) * (2 * u * liftFactor u) := by ring
    _ ≤ (2 * (u * liftFactor u)) * (2 * u * liftFactor u) :=
        Nat.mul_le_mul_right _ hstep
    _ = (2 * u * liftFactor u) * (2 * u * liftFactor u) := by ring

/-! ## The cell of a marker is between one and two fibres long -/

/-- **The fibre fits inside the marker's cell.** -/
theorem lift_fit {β : ℝ} {u p : ℕ} (hu : 0 < u) (hp : liftMarkerScale u < p)
    (hple : p ≤ 2 * liftMarkerScale u) :
    (cardLength β (liftScale u) * (((liftPhysScale u / p : ℕ) : ℝ) + 1) / ((2 * u : ℕ) : ℝ) + 1)
        * (p : ℝ)
      ≤ ((liftWindow β u : ℕ) : ℝ) := by
  have hy0 : (0 : ℝ) < cardLength β (liftScale u) := cardLength_pos _ _
  have hu2 : (0 : ℝ) < ((2 * u : ℕ) : ℝ) := by
    have : (0 : ℕ) < 2 * u := by omega
    exact_mod_cast this
  have hstart := liftStart_lt hu hp
  have hstartR : ((liftPhysScale u / p : ℕ) : ℝ) + 1 ≤ ((2 * u : ℕ) : ℝ) := by
    have : (liftPhysScale u / p) + 1 ≤ 2 * u := by omega
    exact_mod_cast this
  have hquot : cardLength β (liftScale u) * (((liftPhysScale u / p : ℕ) : ℝ) + 1)
      / ((2 * u : ℕ) : ℝ) ≤ cardLength β (liftScale u) := by
    rw [div_le_iff₀ hu2]
    exact mul_le_mul_of_nonneg_left hstartR hy0.le
  have hpR : (0 : ℝ) < (p : ℝ) := by
    have : 0 < p := by omega
    exact_mod_cast this
  have hple : (p : ℝ) ≤ 2 * ((liftMarkerScale u : ℕ) : ℝ) := by exact_mod_cast hple
  have hLbig : cardLength β (liftScale u) + 1 ≤ ((liftCellLen β u : ℕ) : ℝ) := by
    rw [liftCellLen]
    push_cast
    have := Nat.le_ceil (cardLength β (liftScale u))
    linarith
  have hLnn : (0 : ℝ) ≤ ((liftCellLen β u : ℕ) : ℝ) := Nat.cast_nonneg _
  have hMnn : (0 : ℝ) ≤ ((liftMarkerScale u : ℕ) : ℝ) := Nat.cast_nonneg _
  have hwin : ((liftWindow β u : ℕ) : ℝ)
      = 2 * ((liftCellLen β u : ℕ) : ℝ) * ((liftMarkerScale u : ℕ) : ℝ) := by
    rw [liftWindow]
    push_cast
    ring
  rw [hwin]
  calc (cardLength β (liftScale u) * (((liftPhysScale u / p : ℕ) : ℝ) + 1)
          / ((2 * u : ℕ) : ℝ) + 1) * (p : ℝ)
      ≤ (cardLength β (liftScale u) + 1) * (p : ℝ) := by
        exact mul_le_mul_of_nonneg_right (by linarith) hpR.le
    _ ≤ ((liftCellLen β u : ℕ) : ℝ) * (2 * ((liftMarkerScale u : ℕ) : ℝ)) := by
        refine mul_le_mul hLbig hple hpR.le hLnn
    _ = 2 * ((liftCellLen β u : ℕ) : ℝ) * ((liftMarkerScale u : ℕ) : ℝ) := by ring

/-- **The fibre fills at least a fixed fraction of the marker's cell.** -/
theorem lift_supply {β : ℝ} {u p : ℕ} (hu : 0 < u) (hp : liftMarkerScale u < p)
    (hple : p ≤ 2 * liftMarkerScale u) (hM0 : 0 < liftMarkerScale u)
    (hy3 : 3 ≤ cardLength β (liftScale u)) :
    (squarefreeDensity / 256) * (((liftWindow β u : ℕ) : ℝ) / (p : ℝ) - 1)
      ≤ (3 / 16) * squarefreeDensity
          * (cardLength β (liftScale u) * ((liftPhysScale u / p : ℕ) : ℝ)
              / ((2 * u : ℕ) : ℝ) - 1) := by
  have hD : (0 : ℝ) < squarefreeDensity := squarefreeDensity_pos
  have hMR : (0 : ℝ) < ((liftMarkerScale u : ℕ) : ℝ) := by exact_mod_cast hM0
  have hpR : (0 : ℝ) < (p : ℝ) := by
    have : 0 < p := by omega
    exact_mod_cast this
  have hpM : ((liftMarkerScale u : ℕ) : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hu2 : (0 : ℝ) < ((2 * u : ℕ) : ℝ) := by
    have : (0 : ℕ) < 2 * u := by omega
    exact_mod_cast this
  -- the cell is at most `2L`
  have hwin : ((liftWindow β u : ℕ) : ℝ)
      = 2 * ((liftCellLen β u : ℕ) : ℝ) * ((liftMarkerScale u : ℕ) : ℝ) := by
    rw [liftWindow]
    push_cast
    ring
  have hcell : ((liftWindow β u : ℕ) : ℝ) / (p : ℝ) ≤ 2 * ((liftCellLen β u : ℕ) : ℝ) := by
    rw [hwin, div_le_iff₀ hpR]
    have hLnn : (0 : ℝ) ≤ 2 * ((liftCellLen β u : ℕ) : ℝ) := by positivity
    nlinarith [hpM, hLnn]
  have hLle : ((liftCellLen β u : ℕ) : ℝ) ≤ cardLength β (liftScale u) + 2 := by
    rw [liftCellLen]
    push_cast
    have := Nat.ceil_lt_add_one (cardLength_pos β (liftScale u)).le
    linarith
  -- the fibre is at least `hy/2`
  have hstart := liftStart_ge (u := u) (p := p) (by omega) hple
  have hstartR : ((u : ℕ) : ℝ) ≤ ((liftPhysScale u / p : ℕ) : ℝ) := by exact_mod_cast hstart
  have hy0 : (0 : ℝ) < cardLength β (liftScale u) := cardLength_pos _ _
  have hcast2u : ((2 * u : ℕ) : ℝ) = 2 * (u : ℝ) := by push_cast; ring
  have hfib : cardLength β (liftScale u) / 2
      ≤ cardLength β (liftScale u) * ((liftPhysScale u / p : ℕ) : ℝ) / ((2 * u : ℕ) : ℝ) := by
    rw [hcast2u, le_div_iff₀ (by positivity)]
    have huR : (0 : ℝ) < (u : ℝ) := by exact_mod_cast hu
    nlinarith [hstartR, hy0, huR]
  -- combine
  have hnum : (squarefreeDensity / 256) * (((liftWindow β u : ℕ) : ℝ) / (p : ℝ) - 1)
      ≤ (squarefreeDensity / 256) * (2 * (cardLength β (liftScale u) + 2)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    linarith [hcell, hLle]
  have hkey : (squarefreeDensity / 256) * (2 * (cardLength β (liftScale u) + 2))
      ≤ (3 / 16) * squarefreeDensity * (cardLength β (liftScale u) / 2 - 1) := by
    have hgap : (cardLength β (liftScale u) + 2) / 128
        ≤ 3 * cardLength β (liftScale u) / 32 - 3 / 16 := by
      linarith [hy3]
    nlinarith [hgap, hD]
  have hmono : (3 / 16) * squarefreeDensity * (cardLength β (liftScale u) / 2 - 1)
      ≤ (3 / 16) * squarefreeDensity
          * (cardLength β (liftScale u) * ((liftPhysScale u / p : ℕ) : ℝ)
              / ((2 * u : ℕ) : ℝ) - 1) := by
    refine mul_le_mul_of_nonneg_left (by linarith [hfib]) (by positivity)
  linarith [hnum, hkey, hmono]

/-- **The separation of markers sharing a start.** -/
theorem lift_separation {u p q : ℕ} (hu : 0 < u) (hp : 0 < p)
    (hpq : p < q) (hple : p ≤ 2 * liftMarkerScale u)
    (heq : liftPhysScale u / q = liftPhysScale u / p) :
    q ≤ p + 4 * liftFactor u := by
  have hAt : u ≤ liftPhysScale u / p := liftStart_ge hp hple
  have hdiv : liftPhysScale u / (u * u) = 4 * liftFactor u := by
    rw [liftPhysScale, liftMarkerScale,
      show 2 * u * (2 * u * liftFactor u) = (4 * liftFactor u) * (u * u) by ring]
    exact Nat.mul_div_cancel _ (by positivity)
  have := reciprocal_separation (X := liftPhysScale u) (A := u) hu hp hpq hAt heq
  omega

end

end RHTower.Sieve
