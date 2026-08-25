import GaloisForLFunctions.RHTower.IndexedDiagonalWeakSchatten
import GaloisForLFunctions.RHTower.GaussColumnDecay
import GaloisForLFunctions.RHTower.GaussFourierDiagonal
import GaloisForLFunctions.RHTower.GaussPositiveAllDepthCriticalMass
import GaloisForLFunctions.RHTower.WeakSchattenHolder

/-!
# Weak Schatten bounds for the actual Gauss quasi-inner block

The sampled Gauss symbol has exact critical power decay on nonzero integer frequencies.  The
standard zig-zag enumeration of `ℤ` loses only a factor four, so the corresponding Fourier
diagonals belong to weak `S_{2m}`.  Weak Schatten Hölder then places the literal block

`G = p B D B⁻² D* B`

in weak `S_m`, including weak trace class at `m = 1`.
-/

namespace RHTower

open MeasureTheory HTGeometry

noncomputable section

/-- The standard zig-zag index of a nonzero integer is controlled by four times its magnitude. -/
theorem intEquivNat_succ_le_four_mul_natAbs {z : ℤ} (hz : z ≠ 0) :
    Equiv.intEquivNat z + 1 ≤ 4 * z.natAbs := by
  cases z with
  | ofNat n =>
      change 2 * n + 1 ≤ 4 * n
      have hn : n ≠ 0 := by simpa using hz
      omega
  | negSucc n =>
      change 2 * n + 1 + 1 ≤ 4 * (n + 1)
      omega

/-- The sampled Gauss symbol satisfies critical `2m`-power decay in the standard enumeration of
the bilateral frequency lattice. -/
theorem gaussSampleValue_reindex_pow_le {m : ℕ} (hm : 1 ≤ m) (k : Fin m)
    (p : Nat.Primes) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      ‖gaussSampleValue k p (Equiv.intEquivNat.symm n)‖ ^ (2 * m) ≤
        C / ((n : ℝ) + 1) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_gaussSampleValue_pow_mul_natAbs_le hm k p
  refine ⟨4 * C, by positivity, fun n => ?_⟩
  let z : ℤ := Equiv.intEquivNat.symm n
  by_cases hz : z = 0
  · rw [show ‖gaussSampleValue k p (Equiv.intEquivNat.symm n)‖ ^ (2 * m) = 0 by
      simp [z, hz, gaussSampleValue_zero, show 2 * m ≠ 0 by omega]]
    positivity
  · have hmain := hC z hz
    have habs : 0 < (z.natAbs : ℝ) := by exact_mod_cast Int.natAbs_pos.mpr hz
    have hindexNat := intEquivNat_succ_le_four_mul_natAbs hz
    have hindex : (n : ℝ) + 1 ≤ 4 * (z.natAbs : ℝ) := by
      exact_mod_cast (show n + 1 ≤ 4 * z.natAbs by simpa [z] using hindexNat)
    change ‖gaussSampleValue k p z‖ ^ (2 * m) ≤ (4 * C) / ((n : ℝ) + 1)
    calc
      ‖gaussSampleValue k p z‖ ^ (2 * m) ≤ C / (z.natAbs : ℝ) := by
        rw [le_div_iff₀ habs]
        exact hmain
      _ ≤ (4 * C) / ((n : ℝ) + 1) := by
        rw [div_le_div_iff₀ habs (by positivity)]
        nlinarith

/-- The actual unscaled Gauss Fourier diagonal belongs to weak `S_{2m}`. -/
theorem memWeakSchattenClass_gaussDiagonalBlock {m : ℕ} (hm : 1 ≤ m)
    (k : Fin m) (p : Nat.Primes) :
    MemWeakSchattenClass ((2 * m : ℕ) : ℝ) (gaussDiagonalBlock hm k p) := by
  let lam : ℤ → ℂ := fun i => gaussSampleValue k p i
  let M : ℝ := gaussSampleValueBound hm k p
  let hM : ∀ i, ‖lam i‖ ≤ M := norm_gaussSampleValue_le hm k p
  obtain ⟨C, hC0, hdecay⟩ := gaussSampleValue_reindex_pow_le hm k p
  have hdiag : MemWeakSchattenClass ((2 * m : ℕ) : ℝ)
      (ellTwoDiagonal lam hM) :=
    memWeakSchattenClass_ellTwoDiagonal_of_reindex_pow_le
      Equiv.intEquivNat.symm hM (by omega) hC0 hdecay
  have hlp : GaloisForLFunctions.lpDiagonalCLM lam
      (gaussSampleValueBound_nonneg hm k p) hM = ellTwoDiagonal lam hM := by
    ext f i
    rfl
  have hblock : gaussDiagonalBlock hm k p =
      unitaryPush (fourierBasis (T := (1 : ℝ))).repr.symm (ellTwoDiagonal lam hM) := by
    rw [gaussDiagonalBlock, hlp]
    rfl
  rw [hblock]
  exact hdiag.unitaryPush (fourierBasis (T := (1 : ℝ))).repr.symm

/-- The conjugate Gauss Fourier diagonal also belongs to weak `S_{2m}`. -/
theorem memWeakSchattenClass_gaussDiagonalBlockStar {m : ℕ} (hm : 1 ≤ m)
    (k : Fin m) (p : Nat.Primes) :
    MemWeakSchattenClass ((2 * m : ℕ) : ℝ) (gaussDiagonalBlockStar hm k p) := by
  let lam : ℤ → ℂ := fun i => starRingEnd ℂ (gaussSampleValue k p i)
  let M : ℝ := gaussSampleValueBound hm k p
  let hM : ∀ i, ‖lam i‖ ≤ M := norm_conj_gaussSampleValue_le hm k p
  obtain ⟨C, hC0, hdecay⟩ := gaussSampleValue_reindex_pow_le hm k p
  have hdiag : MemWeakSchattenClass ((2 * m : ℕ) : ℝ)
      (ellTwoDiagonal lam hM) :=
    memWeakSchattenClass_ellTwoDiagonal_of_reindex_pow_le
      Equiv.intEquivNat.symm hM (by omega) hC0 (fun n => by
        simpa [lam, Complex.norm_conj] using hdecay n)
  have hlp : GaloisForLFunctions.lpDiagonalCLM lam
      (gaussSampleValueBound_nonneg hm k p) hM = ellTwoDiagonal lam hM := by
    ext f i
    rfl
  have hblock : gaussDiagonalBlockStar hm k p =
      unitaryPush (fourierBasis (T := (1 : ℝ))).repr.symm (ellTwoDiagonal lam hM) := by
    rw [gaussDiagonalBlockStar, hlp]
    rfl
  rw [hblock]
  exact hdiag.unitaryPush (fourierBasis (T := (1 : ℝ))).repr.symm

/-- The full scaled Gauss Fourier diagonal belongs to weak `S_{2m}`. -/
theorem memWeakSchattenClass_gaussDiagonalBlockFull {m : ℕ} (hm : 1 ≤ m)
    (k : Fin m) (p : Nat.Primes) :
    MemWeakSchattenClass ((2 * m : ℕ) : ℝ) (gaussDiagonalBlockFull hm k p) := by
  have hp : 0 < ((2 * m : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2 * m by omega)
  rw [gaussDiagonalBlockFull]
  convert (memWeakSchattenClass_gaussDiagonalBlock hm k p).comp_left hp
      ((((gaussArchScale m : ℝ) : ℂ) • 1)) using 1
  apply ContinuousLinearMap.ext
  intro x
  rfl

/-- The full conjugate Gauss Fourier diagonal belongs to weak `S_{2m}`. -/
theorem memWeakSchattenClass_gaussDiagonalBlockFullStar {m : ℕ} (hm : 1 ≤ m)
    (k : Fin m) (p : Nat.Primes) :
    MemWeakSchattenClass ((2 * m : ℕ) : ℝ) (gaussDiagonalBlockFullStar hm k p) := by
  have hp : 0 < ((2 * m : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2 * m by omega)
  rw [gaussDiagonalBlockFullStar]
  convert (memWeakSchattenClass_gaussDiagonalBlockStar hm k p).comp_left hp
      ((((gaussArchScale m : ℝ) : ℂ) • 1)) using 1
  apply ContinuousLinearMap.ext
  intro x
  rfl

/-- The literal quasi-inner Gauss block belongs to weak `S_m`; at `m = 1` this is weak trace
class without any additional premise. -/
theorem memWeakSchattenClass_gaussQuasiInnerGFull {m : ℕ} (hm : 1 ≤ m)
    (k : Fin m) (p : Nat.Primes) :
    MemWeakSchattenClass (m : ℝ) (gaussQuasiInnerGFull hm k p) := by
  let B := gaussPrimeScaleBlock (show (1 : ℝ) < (p : ℝ) by exact_mod_cast p.prop.one_lt)
  let Binv := gaussPrimeScaleInvSqBlock
    (show (1 : ℝ) < (p : ℝ) by exact_mod_cast p.prop.one_lt)
  let D := gaussDiagonalBlockFull hm k p
  let Dstar := gaussDiagonalBlockFullStar hm k p
  have hP : 0 < ((2 * m : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2 * m by omega)
  have hmR : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hD : MemWeakSchattenClass ((2 * m : ℕ) : ℝ) D :=
    memWeakSchattenClass_gaussDiagonalBlockFull hm k p
  have hDstar : MemWeakSchattenClass ((2 * m : ℕ) : ℝ) Dstar :=
    memWeakSchattenClass_gaussDiagonalBlockFullStar hm k p
  have hprod := (hD.comp_right hP Binv).comp hP hP hDstar
  have hexp :
      (((2 * m : ℕ) : ℝ) * ((2 * m : ℕ) : ℝ) /
        (((2 * m : ℕ) : ℝ) + ((2 * m : ℕ) : ℝ))) = (m : ℝ) := by
    push_cast
    field_simp
    ring
  have hmiddle : MemWeakSchattenClass (m : ℝ) ((D ∘L Binv) ∘L Dstar) := by
    rw [← hexp]
    exact hprod
  have hbounded := ((hmiddle.comp_right hmR B).comp_left hmR B).comp_left hmR
    ((((p : ℝ) : ℂ) • 1))
  rw [gaussQuasiInnerGFull]
  convert hbounded using 1
  ext x
  simp [B, Binv, D, Dstar, ContinuousLinearMap.comp_apply]

/-- The actual depth-one quasi-inner block has sharp Schatten threshold one: it is weak `S₁`, is
not trace class, and belongs to every strictly larger Schatten class. -/
theorem gaussQuasiInnerGFull_one_exact_schattenDepth
    (k : Fin 1) (p : Nat.Primes) :
    (∀ q : ℝ, 0 < q → q ≤ 1 →
        ¬ MemSchattenClass q (gaussQuasiInnerGFull (m := 1) le_rfl k p)) ∧
      (∀ q : ℝ, 1 < q →
        MemSchattenClass q (gaussQuasiInnerGFull (m := 1) le_rfl k p)) := by
  have hweak : MemWeakSchattenClass 1
      (gaussQuasiInnerGFull (m := 1) le_rfl k p) := by
    simpa using memWeakSchattenClass_gaussQuasiInnerGFull (m := 1) le_rfl k p
  have hnot : ¬ MemSchattenClass 1
      (gaussQuasiInnerGFull (m := 1) le_rfl k p) := by
    simpa using gaussQuasiInnerGFull_pow_not_memSchattenClass_one (m := 1) le_rfl k p
  constructor
  · intro q hq hq1 hmem
    exact hnot (hmem.mono hq hq1)
  · intro q h1q
    exact hweak.memSchattenClass_of_lt zero_lt_one h1q

end

end RHTower
