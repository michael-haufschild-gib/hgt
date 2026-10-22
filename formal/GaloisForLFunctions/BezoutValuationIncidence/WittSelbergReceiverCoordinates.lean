import GaloisForLFunctions.RHTower.Deninger.DeningerBigWittFrobeniusRingEndomorphism
import GaloisForLFunctions.BezoutValuationIncidence.SelbergHilbertCoordinateEquivalence

/-!
# Native real Witt ghosts in finite Selberg coordinates

The actual real Big-Witt ghost coordinates are transported by the canonical finite Selberg isometry. Frobenius two, arbitrary positive Verschiebung, and native lag compression have explicit coordinate formulas with their cutoffs retained.
-/

set_option autoImplicit false
open Finset RHTower RHTower.Sieve GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators InnerProductSpace
noncomputable section


namespace GaloisForLFunctions.BezoutValuationIncidence

/-- Literal SC ghost values, including the zero coefficient of the logarithmic series. -/
def nativeWittGhost (w : DeningerBigWittRing ℝ) (q : ℕ) : ℝ :=
  deningerBigWittGhostCoeff (Additive.toMul w.additiveVal) q

theorem nativeWittGhost_frobeniusTwo (w : DeningerBigWittRing ℝ) (q : ℕ) (hq : 0 < q) :
    nativeWittGhost (deningerBigWittFrobeniusTwoRingHom w) q = nativeWittGhost w (2 * q) :=
  deningerBigWittFrobeniusTwoRingHom_ghost w q hq

/-- Verschiebung on the original constant-one power series, by literal substitution T ↦ T^m. -/
def nativeWittVerschiebung (m : ℕ) (hm : m ≠ 0) (w : DeningerBigWittRing ℝ) :
    DeningerBigWittRing ℝ :=
  ⟨Additive.ofMul (deningerBigWittOfSeries
    (PowerSeries.expand m hm (deningerBigWittSeries (Additive.toMul w.additiveVal)))
    (by rw [PowerSeries.constantCoeff_expand, deningerBigWittSeries_constantCoeff]))⟩

theorem nativeWittGhost_verschiebung (m : ℕ) (hm : m ≠ 0)
    (w : DeningerBigWittRing ℝ) (q : ℕ) :
    nativeWittGhost (nativeWittVerschiebung m hm w) q =
      if m ∣ q then (m : ℝ) * nativeWittGhost w (q / m) else 0 := by
  change PowerSeries.coeff q (deningerBigWittLogGhost
    (PowerSeries.expand m hm (deningerBigWittSeries (Additive.toMul w.additiveVal)))
      (by rw [PowerSeries.constantCoeff_expand, deningerBigWittSeries_constantCoeff])) = _
  rw [deningerBigWittLogGhost_expand m hm
    (deningerBigWittSeries (Additive.toMul w.additiveVal))
    (deningerBigWittSeries_constantCoeff (Additive.toMul w.additiveVal)),
    PowerSeries.coeff_C_mul, PowerSeries.coeff_expand]
  split_ifs <;> simp only [nativeWittGhost, deningerBigWittGhostCoeff,
    deningerBigWittGhostSeries, mul_zero]

/-- The finite source receiver: Ramanujan inversion of actual Witt ghost data. -/
def wittSieveReceiver (N : ℕ) (w : DeningerBigWittRing ℝ) : SieveCoefficientSpace N :=
  weightedSelbergInverse N ((EuclideanSpace.equiv (SieveActiveIndex N) ℝ).symm
    (fun q => Real.sqrt (q.val.totient : ℝ) * nativeWittGhost w q.val))

theorem weightedSelberg_wittSieveReceiver (N : ℕ) (w : DeningerBigWittRing ℝ)
    (q : SieveActiveIndex N) :
    weightedSelbergIsometry N (wittSieveReceiver N w) q =
      Real.sqrt (q.val.totient : ℝ) * nativeWittGhost w q.val := by
  exact congrArg (fun x : EuclideanSpace ℝ (SieveActiveIndex N) => x q)
    (weightedSelbergLinear_inverse N _)

theorem selberg_wittSieveReceiver (N : ℕ) (w : DeningerBigWittRing ℝ)
    (q : ℕ) (hq : q ∈ Icc 1 N) :
    selbergMultiplesCoord N (sieveCoefficientExtension N (wittSieveReceiver N w)) q =
      nativeWittGhost w q := by
  have h := weightedSelberg_wittSieveReceiver N w ⟨q, hq⟩
  change Real.sqrt (q.totient : ℝ) *
    selbergMultiplesCoord N (sieveCoefficientExtension N (wittSieveReceiver N w)) q =
      Real.sqrt (q.totient : ℝ) * nativeWittGhost w q at h
  apply mul_left_cancel₀ _ h
  apply (Real.sqrt_pos.mpr _).ne'
  exact_mod_cast Nat.totient_pos.mpr (mem_Icc.mp hq).1

/-- The receiver norm is a genuine native sieve norm, with these exact ghost coordinates. -/
theorem norm_wittSieveReceiver_sq (N : ℕ) (w : DeningerBigWittRing ℝ) :
    ‖wittSieveReceiver N w‖ ^ 2 =
      ∑ q ∈ Icc 1 N, (q.totient : ℝ) * nativeWittGhost w q ^ 2 := by
  rw [norm_sieveCoefficient_sq]
  unfold selbergTotientDiagonalForm
  apply sum_congr rfl
  intro q hq
  rw [selberg_wittSieveReceiver N w q hq]

theorem wittSieveReceiver_add (N : ℕ) (w z : DeningerBigWittRing ℝ) :
    wittSieveReceiver N (w + z) = wittSieveReceiver N w + wittSieveReceiver N z := by
  apply (weightedSelbergIsometry N).injective
  ext q
  rw [map_add]
  change weightedSelbergIsometry N (wittSieveReceiver N (w + z)) q =
    weightedSelbergIsometry N (wittSieveReceiver N w) q +
      weightedSelbergIsometry N (wittSieveReceiver N z) q
  rw [weightedSelberg_wittSieveReceiver, weightedSelberg_wittSieveReceiver,
    weightedSelberg_wittSieveReceiver]
  have hg : nativeWittGhost (w + z) q.val = nativeWittGhost w q.val + nativeWittGhost z q.val :=
    (deningerBigWittGhostComponent q.val (mem_Icc.mp q.property).1).map_add w z
  rw [hg, mul_add]

/-- Frobenius reads a larger original cutoff; no ghost data are invented beyond N. -/
theorem wittSieveReceiver_frobeniusTwo (N : ℕ) (w : DeningerBigWittRing ℝ)
    (q : ℕ) (hq : q ∈ Icc 1 N) :
    selbergMultiplesCoord N
      (sieveCoefficientExtension N (wittSieveReceiver N (deningerBigWittFrobeniusTwoRingHom w))) q =
    selbergMultiplesCoord (2 * N)
      (sieveCoefficientExtension (2 * N) (wittSieveReceiver (2 * N) w)) (2 * q) := by
  rw [selberg_wittSieveReceiver N _ q hq, nativeWittGhost_frobeniusTwo w q (mem_Icc.mp hq).1]
  exact (selberg_wittSieveReceiver (2 * N) w (2 * q) (by
    obtain ⟨hq0, hqN⟩ := mem_Icc.mp hq
    exact mem_Icc.mpr ⟨by omega, by omega⟩)).symm

theorem wittSieveReceiver_verschiebung (N m : ℕ) (hm : m ≠ 0) (w : DeningerBigWittRing ℝ)
    (q : ℕ) (hq : q ∈ Icc 1 N) :
    selbergMultiplesCoord N
      (sieveCoefficientExtension N (wittSieveReceiver N (nativeWittVerschiebung m hm w))) q =
      if m ∣ q then (m : ℝ) * selbergMultiplesCoord N
        (sieveCoefficientExtension N (wittSieveReceiver N w)) (q / m) else 0 := by
  rw [selberg_wittSieveReceiver N _ q hq, nativeWittGhost_verschiebung]
  split_ifs with hd
  · have hdiv : q / m ∈ Icc 1 N := mem_Icc.mpr
      ⟨Nat.div_pos (Nat.le_of_dvd (mem_Icc.mp hq).1 hd) (Nat.pos_of_ne_zero hm),
        (Nat.div_le_self q m).trans (mem_Icc.mp hq).2⟩
    rw [selberg_wittSieveReceiver N w (q / m) hdiv]
  · rfl

/-- Native BVI lag compression acts on these same actual SC ghost values. -/
theorem wittSieveReceiver_lag_prediction (N h : ℕ) (w : DeningerBigWittRing ℝ)
    (q : SieveActiveIndex N) :
    weightedSelbergIsometry N (nativeSieveTranslationPredictor N h (wittSieveReceiver N w)) q =
      sieveLagMultiplier q.val h * Real.sqrt (q.val.totient : ℝ) * nativeWittGhost w q.val := by
  rw [weightedSelbergIsometry_translation, weightedSelberg_wittSieveReceiver, mul_assoc]

end GaloisForLFunctions.BezoutValuationIncidence

end
