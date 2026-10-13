import GaloisForLFunctions.RHTower.FamilyFrobenius
import GaloisForLFunctions.RHTower.FamilyTraceWide
import GaloisForLFunctions.RHTower.ThmEUniformSeam
import GaloisForLFunctions.RHTower.FamilyRankTraceSeam

/-!
# The zero side of the family of characters modulo a prime

For a prime `q` every nontrivial character modulo `q` is primitive (`isPrimitive_of_prime`), so each
`L(s, χ)`, `χ ≠ 1`, carries a zero configuration `famZ q χ`.  At any bandwidth (`ParamsValidFam`) and any height
`T` with `8w ≤ L`:

* the zero-side Gram matrix equals the prime-side one (`GzGpChi_at_fam`, explicit formula for `L(s, χ)`);
* the normalised trace is `N_χ` up to the modulus-uniform trace error (`rtrace_hat_ge_fam`);
* the normalised Frobenius norm is `tr G̃²_χ/(aL)²` (`frobSq_hat_eq_fam`).

These are the per-character inputs of the summed rank–trace seam.
-/

open MeasureTheory Real Set Zeta23 Zeta23.ThmE Zeta23.PrimeSide Zeta23.Assembly RHLinalg

noncomputable section

namespace RHTower

/-- The empty zero configuration. -/
def emptyZeroConfig : ZeroConfig where
  carrier := ∅
  mult := fun _ => 0
  one_le_mult := fun _ h => absurd h (Set.notMem_empty _)
  strip := fun _ h => absurd h (Set.notMem_empty _)
  reflect_mem := fun _ h => absurd h (Set.notMem_empty _)
  mult_reflect := fun _ h => absurd h (Set.notMem_empty _)
  finite_window := fun _ _ => by simp

/-- Every nontrivial character modulo a prime is primitive. -/
theorem isPrimitive_of_prime {q : ℕ} (hq : q.Prime) (χ : DirichletCharacter ℂ q) (h : χ ≠ 1) :
    χ.IsPrimitive := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  rw [DirichletCharacter.isPrimitive_def]
  rcases (Nat.dvd_prime hq).mp (DirichletCharacter.conductor_dvd_level χ) with h1 | h1
  · exact absurd ((DirichletCharacter.eq_one_iff_conductor_eq_one).mpr h1) h
  · exact h1

open Classical in
/-- The zero configuration of `L(s, χ)` for a primitive `χ` (empty otherwise). -/
def famZ {q : ℕ} [NeZero q] (hq : 1 < q) (χ : DirichletCharacter ℂ q) : ZeroConfig :=
  if h : χ.IsPrimitive then LZeros (LSeam_of hq h) else emptyZeroConfig

theorem famZ_of_prim {q : ℕ} [NeZero q] (hq : 1 < q) {χ : DirichletCharacter ℂ q}
    (h : χ.IsPrimitive) : famZ hq χ = LZeros (LSeam_of hq h) := by
  unfold famZ; rw [dif_pos h]

variable {P : Params} {T : ℝ}

/-- **The explicit-formula bridge at any bandwidth.** -/
theorem GzGpChi_at_fam {Z : ZeroConfig} {κ q : ℕ} {c : ℕ → ℂ} (hP : ParamsValidFam P)
    (hEF : ExplicitFormulaPaperChi κ q c Z) (hL : 0 < P.L T) (hwL : 8 * P.w ≤ P.L T) :
    Z.Gz P T = GpChi P κ q c T := by
  refine Z.Gz_eq_GpChi P κ q c T hEF hL ?_ ?_
  · exact (Complex.ofRealCLM.contDiff.comp
      (Taper.phi_contDiff hP.taper hP.w_pos (hP.two_w_le hwL))).of_le (by norm_num)
  · exact closure_minimal (Taper.phi_support_subset hP.taper hP.w_pos) isClosed_Icc

/-- The normalised Frobenius norm of the zero-side matrix of a primitive character. -/
theorem frobSq_hat_eq_fam {q : ℕ} [NeZero q] (hq : 1 < q) {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hP : ParamsValidFam P) (hL : 0 < P.L T) (hwL : 8 * P.w ≤ P.L T) :
    frobSq (P.hat T ((famZ hq χ).Gz P T))
      = ((P.a T * P.L T)⁻¹) ^ 2 * trGt2ChiA (parity χ) q (coeff χ) (P.toSetting T) (P.localFun T) := by
  rw [famZ_of_prim hq hprim,
    GzGpChi_at_fam hP (paperInputsChi_L hq hprim).EF hL hwL, frobSq_hat, frobSq_tilde_GpChi]
  rfl

/-- The normalised trace of the zero-side matrix of a primitive character. -/
theorem rtrace_hat_eq_fam {q : ℕ} [NeZero q] (hq : 1 < q) {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hP : ParamsValidFam P) (hL : 0 < P.L T) (hwL : 8 * P.w ≤ P.L T) :
    rtrace (P.hat T ((famZ hq χ).Gz P T))
      = (P.a T * P.L T)⁻¹ * trGtChiA (parity χ) q (coeff χ) (P.toSetting T) (P.localFun T) := by
  rw [famZ_of_prim hq hprim,
    GzGpChi_at_fam hP (paperInputsChi_L hq hprim).EF hL hwL, rtrace_hat, rtrace_tilde_GpChi]
  rfl

/-- **Trace lower bound per character.** -/
theorem rtrace_hat_ge_fam {q : ℕ} [NeZero q] (hq : 1 < q) {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hP : ParamsValidFam P) (hL : 0 < P.L T) (hwL : 8 * P.w ≤ P.L T)
    (ha : 0 < P.a T) {E : ℝ}
    (htr : |trGtChiA (parity χ) q (coeff χ) (P.toSetting T) (P.localFun T)
      - P.a T * P.L T * ((famZ hq χ).N T (2 * T) : ℝ)| ≤ P.L T * E) :
    ((famZ hq χ).N T (2 * T) : ℝ) - E / P.a T ≤ rtrace (P.hat T ((famZ hq χ).Gz P T)) := by
  rw [rtrace_hat_eq_fam hq hprim hP hL hwL]
  have h1 := (abs_le.mp htr).1
  have haL : 0 < P.a T * P.L T := mul_pos ha hL
  obtain ⟨t, ht⟩ : ∃ t, t = trGtChiA (parity χ) q (coeff χ) (P.toSetting T) (P.localFun T) := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n : ℝ, n = ((famZ hq χ).N T (2 * T) : ℝ) := ⟨_, rfl⟩
  rw [← ht, ← hn] at h1 ⊢
  have ha0 := ha.ne'
  have hL0 := hL.ne'
  calc n - E / P.a T = (P.a T * P.L T)⁻¹ * (P.a T * P.L T * n - P.L T * E) := by
        field_simp
    _ ≤ (P.a T * P.L T)⁻¹ * t :=
        mul_le_mul_of_nonneg_left (by linarith only [h1]) (inv_nonneg.mpr haL.le)

end RHTower
