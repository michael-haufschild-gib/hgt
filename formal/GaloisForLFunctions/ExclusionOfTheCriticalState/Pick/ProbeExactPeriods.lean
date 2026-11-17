import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.ProbeSpectralMapping
import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.ChebyshevLeakage
import Mathlib.FieldTheory.Minpoly.Field

/-!
# Exact periods of the finite reflection walk

A fixed compressed Chebyshev vector has no leakage and hence is fixed by
the full walk power. Reversibility then propagates fixedness from the
original probes to their reflected span. Thus every period is detected by
a polynomial identity on the smaller signal space.
-/

noncomputable section
open _root_.Polynomial
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
variable {N : ℕ} (p : Fin N → {x : ℝ // 1 ≤ x})

private theorem walk_reversible : walk p * zeroReflection * walk p = zeroReflection := by
  have hQ := _root_.HTGeometry.projectionReflection_sq_eq_one
    (probeProjection p) (probeSpace p).isIdempotentElem_starProjection
  calc
    _ = zeroReflection * _root_.HTGeometry.projectionReflection (probeProjection p) *
        (zeroReflection * zeroReflection) *
          _root_.HTGeometry.projectionReflection (probeProjection p) := by
      simp only [walk, mul_assoc]
    _ = _ := by rw [zeroReflection_sq, mul_one, mul_assoc, hQ, mul_one]

private theorem walk_pow_reversible (n : ℕ) :
    walk p ^ n * zeroReflection * walk p ^ n = zeroReflection := by
  induction n with
  | zero => simp only [pow_zero, one_mul, mul_one]
  | succ n ih =>
    calc
      _ = (walk p * walk p ^ n) * zeroReflection * (walk p ^ n * walk p) :=
        congrArg₂ (fun A B : ZeroSpace →L[ℂ] ZeroSpace => A * zeroReflection * B)
          (pow_succ' (walk p) n) (pow_succ (walk p) n)
      _ = walk p * (walk p ^ n * zeroReflection * walk p ^ n) * walk p := by
        simp only [mul_assoc]
      _ = _ := by rw [ih, walk_reversible]

/-- A compressed fixed vector is an actual fixed vector; equality leaves no orthogonal leakage. -/
theorem chebyshev_fixed_iff_walk_fixed (n : ℕ) {x : ZeroSpace} (hx : x ∈ probeSpace p) :
    aeval (signal p) (Chebyshev.T ℂ (n : ℤ)) x = x ↔ (walk p ^ n) x = x := by
  constructor
  · intro h
    have hr := (chebyshev_norm_eq_iff_return p n hx).mp (congrArg norm h)
    rw [chebyshev_apply_eq_projected_walk p n hx] at h
    have hQ : probeProjection p ((walk p ^ n) x) = (walk p ^ n) x :=
      Submodule.starProjection_eq_self_iff.mpr hr
    rwa [hQ] at h
  · intro h
    rw [chebyshev_apply_eq_projected_walk p n hx, h]
    exact Submodule.starProjection_eq_self_iff.mpr hx

/-- A period on the probe span propagates to its full reflection hull. -/
theorem walk_period_iff_chebyshev_fixed (n : ℕ) :
    hullWalk p ^ n = 1 ↔
      ∀ x ∈ probeSpace p, aeval (signal p) (Chebyshev.T ℂ (n : ℤ)) x = x := by
  constructor
  · intro h x hx
    apply (chebyshev_fixed_iff_walk_fixed p n hx).mpr
    have he := LinearMap.congr_fun h (⟨x, probeSpace_le_reflectionHull p hx⟩ : reflectionHull p)
    have hc := congrArg (fun y : reflectionHull p => (y : ZeroSpace)) he
    simpa only [hullWalk_pow_apply, Module.End.one_apply] using hc
  · intro h
    have hu (x : ZeroSpace) (hx : x ∈ probeSpace p) : (walk p ^ n) x = x :=
      (chebyshev_fixed_iff_walk_fixed p n hx).mp (h x hx)
    have hr (x : ZeroSpace) (hx : x ∈ probeSpace p) :
        (walk p ^ n) (zeroReflection x) = zeroReflection x := by
      have he := congrArg (fun T : ZeroSpace →L[ℂ] ZeroSpace => T x) (walk_pow_reversible p n)
      change (walk p ^ n) (zeroReflection ((walk p ^ n) x)) = zeroReflection x at he
      rwa [hu x hx] at he
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rw [hullWalk_pow_apply]
    obtain ⟨u, hu', v, hv, huv⟩ := Submodule.mem_sup.mp x.property
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv
    change u + zeroReflection w = (x : ZeroSpace) at huv
    change (walk p ^ n) (x : ZeroSpace) = (x : ZeroSpace)
    rw [← huv, map_add, hu u hu', hr w hw]

private theorem probeSignal_pow_coe (n : ℕ) (x : probeSpace p) :
    ((probeSignal p ^ n) x : ZeroSpace) = (signal p ^ n) (x : ZeroSpace) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pow_succ', Module.End.mul_apply, _root_.mul_apply_eq_comp]
    change probeProjection p (zeroReflection (((probeSignal p ^ n) x : probeSpace p) : ZeroSpace)) =
      probeProjection p (zeroReflection (probeProjection p ((signal p ^ n) (x : ZeroSpace))))
    have hQ : probeProjection p (((probeSignal p ^ n) x : probeSpace p) : ZeroSpace) =
        ((probeSignal p ^ n) x : ZeroSpace) :=
      Submodule.starProjection_eq_self_iff.mpr ((probeSignal p ^ n) x).property
    rw [← ih, hQ]

/-- Polynomial evaluation commutes with inclusion of the finite signal space. -/
theorem probeSignal_aeval_coe (P : ℂ[X]) (x : probeSpace p) :
    (aeval (probeSignal p) P x : ZeroSpace) = aeval (signal p) P (x : ZeroSpace) := by
  simp only [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum,
    LinearMap.sum_apply, _root_.sum_apply, Submodule.coe_sum,
    Module.End.mul_apply, _root_.mul_apply_eq_comp,
    Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, _root_.smul_apply,
    Module.End.one_apply, _root_.one_apply_eq_self, Submodule.coe_smul, probeSignal_pow_coe]

/-- Every period is detected by a Chebyshev identity on the smaller compressed signal. -/
theorem walk_period_iff_signal_chebyshev (n : ℕ) :
    hullWalk p ^ n = 1 ↔ aeval (probeSignal p) (Chebyshev.T ℂ (n : ℤ)) = 1 := by
  rw [walk_period_iff_chebyshev_fixed]
  constructor
  · intro h
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rw [probeSignal_aeval_coe]
    exact h x x.property
  · intro h x hx
    have he := LinearMap.congr_fun h (⟨x, hx⟩ : probeSpace p)
    have hc := congrArg (fun y : probeSpace p => (y : ZeroSpace)) he
    simpa only [probeSignal_aeval_coe, Module.End.one_apply] using hc

/-- The minimal polynomial of the signal classifies every exact period of the walk. -/
theorem walk_period_iff_minpoly_dvd (n : ℕ) :
    hullWalk p ^ n = 1 ↔ minpoly ℂ (probeSignal p) ∣ Chebyshev.T ℂ (n : ℤ) - 1 := by
  rw [walk_period_iff_signal_chebyshev, minpoly.dvd_iff, map_sub, map_one, sub_eq_zero]

#print axioms walk_period_iff_minpoly_dvd
#print axioms walk_period_iff_signal_chebyshev
#print axioms walk_period_iff_chebyshev_fixed
#print axioms chebyshev_fixed_iff_walk_fixed
end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
