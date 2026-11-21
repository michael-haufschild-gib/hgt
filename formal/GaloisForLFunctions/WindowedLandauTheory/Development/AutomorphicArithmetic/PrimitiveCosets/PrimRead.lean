import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.PrimitiveCosets.CoreAtH
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.PrimitiveCosets.ToEBij
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.PrimitiveCosets.GzEq
import GaloisForLFunctions.WindowedLandauTheory.SizeWindowBrackets.ChainSlopeWindows.PrimitiveValues

/-! The primitive character realizing each host character and its Cesàro sum. -/

open UpperTheory.Comparison₂ Deduction.CH WindowedLandauTheory WindowedLandauTheory.HC WindowedLandauTheory.D5 WindowedLandauTheory.RankGapBounds.WeightedMeanData WindowedLandauTheory.LFunctionChainParameters.WeightedSlopeBounds WindowedLandauTheory.LFunctionChainParameters.characterSumData WindowedLandauTheory.LFunctionChainParameters.ThickSetMeanBounds WindowedLandauTheory.LFunctionChainParameters.LErr
  WindowedLandauTheory.LFunctionChainParameters.LChain WindowedLandauTheory.LFunctionChainParameters.LHost

private theorem UpperTheory.Comparison₂.prim_read_dir (φ : Frame) (H : HostRaw φ) (ψ : AddChar (E0 × φ.A) ℂ) :
    H.dir (chr φ ψ) = dirChar (recH H) ψ := by
  refine MulChar.ext fun u => ?_
  rw [H.dir_unit, dirChar_unit]
  rfl

private theorem UpperTheory.Comparison₂.prim_read_max (y : ℝ) (n : ℕ) (hn : n ∈ Finset.Icc 1 ⌊y⌋₊) :
    max (y / n - 1) 0 = y / n - 1 := by
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hn
  have hpos : (0 : ℝ) < n := by exact_mod_cast h1
  have hfl : 0 < ⌊y⌋₊ := by omega
  have hy : 1 ≤ y := Nat.floor_pos.mp hfl
  have hny : (n : ℝ) ≤ y := (Nat.cast_le.mpr h2).trans (Nat.floor_le (by linarith))
  have h1y : 1 ≤ y / n := (one_le_div hpos).mpr hny
  exact max_eq_left (by linarith)

private theorem UpperTheory.Comparison₂.prim_read_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    χ.primitiveCharacter = 1 ↔ χ = 1 := by
  constructor
  · intro h
    rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h, map_one]
  · rintro rfl
    exact DirichletCharacter.primitiveCharacter_one

theorem UpperTheory.Comparison₂.prim_read :
    ∀ (φ : Frame) (H : HostAx φ) (ell : AddChar (E0 × φ.A) ℂ → ℂ), HostAddCharCompatible H.toHostRaw ell → ∀ ψ : AddChar (E0 × φ.A) ℂ,
      (ψ ≠ 0 → ell ψ = An.logDerivativeAtOne (H.toHostRaw.prim (chr φ ψ)).χ) ∧
        ∀ y, GPsi (arith H.toHostRaw) ell ψ y = An.gChi (H.toHostRaw.prim (chr φ ψ)).χ y := by
  intro φ H ell hell ψ
  unfold HostAddCharCompatible at hell
  set R := H.toHostRaw with hR
  have hdir : R.dir (chr φ ψ) = dirChar (recH R) ψ := prim_read_dir φ R ψ
  have hval : ∀ n : ℕ, n ≠ 0 → (R.prim (chr φ ψ)).χ n = primVal (arith R) ψ n := by
    intro n hn
    show (R.dir (chr φ ψ)).primitiveCharacter n = _
    rw [hdir]
    exact (primitive_value_primitive (H := φ.A) R.condN R.q R.d (recH R) ψ n
      (HostRaw.condN_pos R).ne' hn).symm
  have h1 : ψ ≠ 0 → ell ψ = An.logDerivativeAtOne (R.prim (chr φ ψ)).χ := fun hψ =>
    @hell ψ hψ _ (R.prim (chr φ ψ)).ne _ (R.prim (chr φ ψ)).prim hval
  have hone : (R.prim (chr φ ψ)).χ = 1 ↔ ψ = 0 := by
    show (R.dir (chr φ ψ)).primitiveCharacter = 1 ↔ ψ = 0
    rw [prim_read_one, hdir]
    constructor
    · intro h
      rw [AddChar.eq_zero_iff]
      intro x
      obtain ⟨g, hg⟩ := (toE_bij φ).1.surjective (Multiplicative.ofAdd x)
      obtain ⟨u, hu⟩ := HostDer.art_surj H.der g
      have hu1 : (dirChar (recH R) ψ) u = 1 := by
        rw [h]
        exact MulChar.one_apply_coe u
      rw [dirChar_unit] at hu1
      have e : recH R u = Multiplicative.ofAdd x := by
        show toE φ (R.art u) = _
        rw [hu, hg]
      rwa [e, toAdd_ofAdd] at hu1
    · rintro rfl
      refine MulChar.ext fun u => ?_
      rw [dirChar_unit, AddChar.zero_apply, MulChar.one_apply_coe]
  refine ⟨h1, fun y => ?_⟩
  by_cases hψ : ψ = 0
  · have hχ : (R.prim (chr φ ψ)).χ = 1 := hone.mpr hψ
    unfold GPsi An.gChi
    rw [if_pos hψ, if_pos hχ, Gz_eq]
  · have hχ : (R.prim (chr φ ψ)).χ ≠ 1 := fun h => hψ (hone.mp h)
    unfold GPsi An.gChi
    rw [if_neg hψ, if_neg hχ, ← h1 hψ, An.sumLamChi]
    congr 1
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : n ≠ 0 := by
      have := (Finset.mem_Icc.mp hn).1
      omega
    rw [hval n hn0, prim_read_max y n hn]
