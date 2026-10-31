import GaloisForLFunctions.HTGeometry.LoopEisenstein.UnipotentCoefficientGroup

/-!
# Ordered coefficients of completed unipotent matrices

The stream lists upper-right, lower-left and upper-left coefficients as
`b₀,c₁,a₁,b₁,c₂,a₂,…`. These are free coordinates over every commutative
ring. This order places every nonlinear multiplication term before the
coordinate whose product it corrects.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein
open Matrix
noncomputable section
variable (R : Type*) [CommRing R]

/-- The principal upper-left series of a free coefficient stream. -/
def streamUpperLeft (x : ℕ → R) : PowerSeries R :=
  PowerSeries.mk fun n => match n with | 0 => 1 | m + 1 => x (3 * m + 2)

/-- The unrestricted upper-right series of a free coefficient stream. -/
def streamUpperRight (x : ℕ → R) : PowerSeries R :=
  PowerSeries.mk fun n => x (3 * n)

/-- The lower-left series, whose constant coefficient is zero. -/
def streamLowerLeft (x : ℕ → R) : PowerSeries R :=
  PowerSeries.mk fun n => match n with | 0 => 0 | m + 1 => x (3 * m + 1)

private theorem streamUpperLeft_zero (x : ℕ → R) :
    PowerSeries.constantCoeff (streamUpperLeft R x) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, streamUpperLeft, PowerSeries.coeff_mk]

private theorem streamLowerLeft_zero (x : ℕ → R) :
    PowerSeries.constantCoeff (streamLowerLeft R x) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, streamLowerLeft, PowerSeries.coeff_mk]

/-- Decode the three free entries from their interlaced stream. -/
def streamToUnipotentCoordinates (x : ℕ → R) : UnipotentCoefficientCoordinates R :=
  (⟨streamUpperLeft R x, streamUpperLeft_zero R x⟩,
    streamUpperRight R x, ⟨streamLowerLeft R x, streamLowerLeft_zero R x⟩)

/-- Interlace the three free entries in their triangular order. -/
def unipotentCoordinatesToStream (p : UnipotentCoefficientCoordinates R) (n : ℕ) : R :=
  if n % 3 = 0 then PowerSeries.coeff (n / 3) p.2.1
  else if n % 3 = 1 then PowerSeries.coeff (n / 3 + 1) (p.2.2 : PowerSeries R)
  else PowerSeries.coeff (n / 3 + 1) (p.1 : PowerSeries R)

@[simp] theorem unipotentCoordinatesToStream_upperRight
    (p : UnipotentCoefficientCoordinates R) (n : ℕ) :
    unipotentCoordinatesToStream R p (3 * n) = PowerSeries.coeff n p.2.1 := by
  have hm : (3 * n) % 3 = 0 := by omega
  have hd : (3 * n) / 3 = n := by omega
  simp only [unipotentCoordinatesToStream, hm, hd, if_true]

@[simp] theorem unipotentCoordinatesToStream_lowerLeft
    (p : UnipotentCoefficientCoordinates R) (n : ℕ) :
    unipotentCoordinatesToStream R p (3 * n + 1) =
      PowerSeries.coeff (n + 1) (p.2.2 : PowerSeries R) := by
  have hm : (3 * n + 1) % 3 = 1 := by omega
  have hd : (3 * n + 1) / 3 = n := by omega
  simp only [unipotentCoordinatesToStream, hm, hd, Nat.one_ne_zero, if_false, if_true]

@[simp] theorem unipotentCoordinatesToStream_upperLeft
    (p : UnipotentCoefficientCoordinates R) (n : ℕ) :
    unipotentCoordinatesToStream R p (3 * n + 2) =
      PowerSeries.coeff (n + 1) (p.1 : PowerSeries R) := by
  have hm : (3 * n + 2) % 3 = 2 := by omega
  have hd : (3 * n + 2) / 3 = n := by omega
  have h20 : (2 : ℕ) ≠ 0 := by omega
  have h21 : (2 : ℕ) ≠ 1 := by omega
  simp only [unipotentCoordinatesToStream, hm, hd, h20, h21, if_false]

private theorem stream_coordinates_left (p : UnipotentCoefficientCoordinates R) :
    streamToUnipotentCoordinates R (unipotentCoordinatesToStream R p) = p := by
  apply Prod.ext
  · apply Subtype.ext
    apply PowerSeries.ext
    intro n
    cases n with
    | zero =>
      simpa only [PowerSeries.coeff_zero_eq_constantCoeff, streamToUnipotentCoordinates] using
        (streamUpperLeft_zero R (unipotentCoordinatesToStream R p)).trans p.1.property.symm
    | succ n =>
      change PowerSeries.coeff (n + 1)
        (streamUpperLeft R (unipotentCoordinatesToStream R p)) =
          PowerSeries.coeff (n + 1) (p.1 : PowerSeries R)
      rw [streamUpperLeft, PowerSeries.coeff_mk]
      exact unipotentCoordinatesToStream_upperLeft R p n
  · apply Prod.ext
    · apply PowerSeries.ext
      intro n
      change PowerSeries.coeff n (streamUpperRight R (unipotentCoordinatesToStream R p)) =
        PowerSeries.coeff n p.2.1
      rw [streamUpperRight, PowerSeries.coeff_mk]
      exact unipotentCoordinatesToStream_upperRight R p n
    · apply Subtype.ext
      apply PowerSeries.ext
      intro n
      cases n with
      | zero =>
        simpa only [PowerSeries.coeff_zero_eq_constantCoeff, streamToUnipotentCoordinates] using
          (streamLowerLeft_zero R (unipotentCoordinatesToStream R p)).trans p.2.2.property.symm
      | succ n =>
        change PowerSeries.coeff (n + 1)
          (streamLowerLeft R (unipotentCoordinatesToStream R p)) =
            PowerSeries.coeff (n + 1) (p.2.2 : PowerSeries R)
        rw [streamLowerLeft, PowerSeries.coeff_mk]
        exact unipotentCoordinatesToStream_lowerLeft R p n

private theorem stream_coordinates_right (x : ℕ → R) :
    unipotentCoordinatesToStream R (streamToUnipotentCoordinates R x) = x := by
  funext n
  have hcases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hcases with h | h | h
  · have he : n = 3 * (n / 3) := by omega
    rw [he, unipotentCoordinatesToStream_upperRight]
    change PowerSeries.coeff (n / 3) (streamUpperRight R x) = _
    rw [streamUpperRight, PowerSeries.coeff_mk]
  · have he : n = 3 * (n / 3) + 1 := by omega
    rw [he, unipotentCoordinatesToStream_lowerLeft]
    change PowerSeries.coeff (n / 3 + 1) (streamLowerLeft R x) = _
    rw [streamLowerLeft, PowerSeries.coeff_mk]
  · have he : n = 3 * (n / 3) + 2 := by omega
    rw [he, unipotentCoordinatesToStream_upperLeft]
    change PowerSeries.coeff (n / 3 + 1) (streamUpperLeft R x) = _
    rw [streamUpperLeft, PowerSeries.coeff_mk]

/-- Ordered coefficients are actual unrestricted coordinates on the completed unipotent group. -/
def unipotentCoefficientStreamEquiv : unipotentCoefficientGroup R ≃ (ℕ → R) :=
  (unipotentCoefficientEquiv R).trans
    { toFun := unipotentCoordinatesToStream R
      invFun := streamToUnipotentCoordinates R
      left_inv := stream_coordinates_left R
      right_inv := stream_coordinates_right R }

end
end GaloisForLFunctions.HTGeometry.LoopEisenstein

#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.unipotentCoefficientStreamEquiv
