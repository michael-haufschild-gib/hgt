import GaloisForLFunctions.RHTower.EulerLogPrimePowerHerglotz
import GaloisForLFunctions.HTGeometry.PrimeClockPolynomialSaturation

/-!
# Discrete support of the Euler-log prime-power Herglotz carrier

The Euler-log atom at `(p,k)` lies at `(k+1) log p`, equivalently at the logarithm of the
integer prime power `p^(k+1)`.  Unique factorization therefore makes the support simple, and its
intersection with every bounded left interval is finite.  This supplies the discrete-support part
of the normalized Euler-log Herglotz carrier; weighted summability is deliberately separate.
-/

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- The real support coordinate of the normalized Euler-log prime-power atom. -/
def eulerLogPrimePowerSupport (x : PrimePowerClockIndex) : ℝ :=
  eulerLogPrimePowerTime x.1 x.2

/-- The Euler-log support point is the logarithm of its represented integer prime power. -/
theorem eulerLogPrimePowerSupport_eq_log_prodNatEquiv (x : PrimePowerClockIndex) :
    eulerLogPrimePowerSupport x =
      Real.log ((Nat.Primes.prodNatEquiv x : ℕ) : ℝ) := by
  rcases x with ⟨p, k⟩
  rw [eulerLogPrimePowerSupport, eulerLogPrimePowerTime,
    Nat.Primes.coe_prodNatEquiv_apply, Nat.cast_pow, Real.log_pow]

/-- The real Euler-log support agrees with the real part of the existing complex prime-power
clock. -/
theorem eulerLogPrimePowerSupport_eq_primePowerClockWeight_re (x : PrimePowerClockIndex) :
    eulerLogPrimePowerSupport x = (primePowerClockWeight x).re := by
  rw [eulerLogPrimePowerSupport_eq_log_prodNatEquiv]
  change Real.log ((Nat.Primes.prodNatEquiv x : ℕ) : ℝ) =
    (Real.log ((Nat.Primes.prodNatEquiv x : ℕ) : ℝ) : ℂ).re
  rfl

/-- Unique factorization makes distinct Euler-log prime-power atoms have distinct support points. -/
theorem eulerLogPrimePowerSupport_injective : Function.Injective eulerLogPrimePowerSupport := by
  intro x y hxy
  have hlog : Real.log ((Nat.Primes.prodNatEquiv x : ℕ) : ℝ) =
      Real.log ((Nat.Primes.prodNatEquiv y : ℕ) : ℝ) := by
    rw [← eulerLogPrimePowerSupport_eq_log_prodNatEquiv x,
      ← eulerLogPrimePowerSupport_eq_log_prodNatEquiv y]
    exact hxy
  have hpowReal : ((Nat.Primes.prodNatEquiv x : ℕ) : ℝ) =
      ((Nat.Primes.prodNatEquiv y : ℕ) : ℝ) :=
    Real.strictMonoOn_log.injOn
      (Set.mem_Ioi.mpr (Nat.cast_pos.mpr (Nat.Primes.prodNatEquiv x).2.pos))
      (Set.mem_Ioi.mpr (Nat.cast_pos.mpr (Nat.Primes.prodNatEquiv y).2.pos)) hlog
  have hpow : (Nat.Primes.prodNatEquiv x : ℕ) = (Nat.Primes.prodNatEquiv y : ℕ) :=
    Nat.cast_injective hpowReal
  apply Nat.Primes.prodNatEquiv.injective
  exact Subtype.ext hpow

/-- The Euler-log prime-power support is locally finite on every left-bounded real interval. -/
theorem finite_eulerLogPrimePowerSupport_le (R : ℝ) :
    Set.Finite {x : PrimePowerClockIndex | eulerLogPrimePowerSupport x ≤ R} := by
  let N : ℕ := ⌈Real.exp R⌉₊
  let f : PrimePowerClockIndex → ℕ := fun x => (Nat.Primes.prodNatEquiv x : ℕ)
  have hf : Function.Injective f := by
    intro x y hxy
    apply Nat.Primes.prodNatEquiv.injective
    exact Subtype.ext hxy
  have hfinite : Set.Finite {x : PrimePowerClockIndex | f x ≤ N} := by
    change (f ⁻¹' Set.Iic N).Finite
    exact (Set.finite_Iic N).preimage (Set.injOn_of_injective hf)
  apply hfinite.subset
  intro x hx
  change f x ≤ N
  have hlog : Real.log ((f x : ℕ) : ℝ) ≤ R := by
    rw [← eulerLogPrimePowerSupport_eq_log_prodNatEquiv x]
    exact hx
  have hpos : 0 < (f x : ℝ) := by
    exact_mod_cast (Nat.Primes.prodNatEquiv x).2.pos
  have hreal : (f x : ℝ) ≤ Real.exp R := by
    calc
      (f x : ℝ) = Real.exp (Real.log ((f x : ℕ) : ℝ)) := (Real.exp_log hpos).symm
      _ ≤ Real.exp R := Real.exp_le_exp.mpr hlog
  have hceil : (f x : ℝ) ≤ (N : ℝ) :=
    hreal.trans (Nat.le_ceil (Real.exp R))
  exact_mod_cast hceil

end

end GaloisForLFunctions.RHTower
