import GaloisForLFunctions.RigidArithmeticOfCuts.TheHierarchyOfLedgers
import GaloisForLFunctions.RHTower.ZetaLogDerivResidue

/-!
# The twin at every degree

Do polynomial ledgers of higher degree read anything of the twin beyond values of `ζ′/ζ` at integers `≥ 2`? The symbol answers this at
every degree. The twin `−λΛ` has symbol

`T(s) = A(s) − 2 A(2s)`, with `A = −ζ′/ζ` (`twinSymbol`),

and `h(s) = −2 A(2s)` is holomorphic on `Re s > ½`. Everything follows from this one line.

* **At a zero nothing separates.** For a zero `ρ` with `Re ρ > ½`, `(s − ρ)^k (T^k − A^k) → 0` for every `k`
  (`tendsto_sub_pow_twinSymbol_at_zero`). The twin and `Λ` have the same leading singular part at each zero, at each degree.
  No ledger separates them there.
* **At the pole the separation reads `s = 2`.** `(s − 1)^{k−1} (T^k − A^k) → −2 k κ` with `κ = A(2) = −ζ′/ζ(2)`
  (`tendsto_sub_pow_twinSymbol_at_one`). At `k = 2` this is the gap `4 L κ N` of the Selberg ledger.

So the nonlinear reading of the twin is a statement at `s = 1` and `s = 2`, at every degree, and parity at the zeros is invisible to all of them.
-/

open Complex Filter Topology

noncomputable section

namespace GaloisForLFunctions.RigidArithmeticOfCuts

/-- The symbol of the Liouville twin: `T(s) = A(s) − 2 A(2s)`. -/
def twinSymbol (s : ℂ) : ℂ := vonMangoldtSymbol s - 2 * vonMangoldtSymbol (2 * s)

/-- The correction `h(s) = −2 A(2s)`, holomorphic on `Re s > ½`. -/
def twinCorrection (s : ℂ) : ℂ := -2 * vonMangoldtSymbol (2 * s)

theorem twinSymbol_eq (s : ℂ) : twinSymbol s = vonMangoldtSymbol s + twinCorrection s := by
  rw [twinSymbol, twinCorrection]
  ring

theorem vonMangoldtSymbol_eq (s : ℂ) :
    vonMangoldtSymbol s = -deriv riemannZeta s / riemannZeta s := by
  rw [vonMangoldtSymbol, logDeriv_apply]
  ring

/-- The correction is continuous on `Re s > ½`, since `2s` lies in the half-plane of absolute convergence. -/
theorem continuousAt_twinCorrection {s : ℂ} (hs : 1 / 2 < s.re) : ContinuousAt twinCorrection s := by
  have h2 : 1 < (2 * s).re := by
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    linarith
  have hd := _root_.RHTower.differentiableAt_neg_logDeriv_riemannZeta_of_one_lt_re h2
  have hfun : twinCorrection = (fun s => -2 * ((fun z => -deriv riemannZeta z / riemannZeta z) (2 * s))) := by
    funext z
    rw [twinCorrection, vonMangoldtSymbol_eq]
  rw [hfun]
  refine (continuousAt_const.mul ?_)
  exact ContinuousAt.comp (f := fun z : ℂ => 2 * z) hd.continuousAt (by fun_prop)

/-- The value of the correction at `s = 1`, in terms of `κ = A(2)`. -/
theorem twinCorrection_one : twinCorrection 1 = -2 * vonMangoldtSymbol 2 := by
  rw [twinCorrection, mul_one]

/-- The residue of `A` at `s = 1`. -/
theorem tendsto_mul_vonMangoldtSymbol_one :
    Tendsto (fun s => (s - 1) * vonMangoldtSymbol s) (𝓝[≠] 1) (𝓝 1) := by
  refine _root_.RHTower.neg_logDeriv_zeta_residue.congr fun s => ?_
  rw [vonMangoldtSymbol_eq]

/-- **At the pole the separation reads `s = 2`, at every degree.** -/
theorem tendsto_sub_pow_twinSymbol_at_one (k : ℕ) :
    Tendsto (fun s => (s - 1) ^ k * (twinSymbol s ^ (k + 1) - vonMangoldtSymbol s ^ (k + 1))) (𝓝[≠] 1)
      (𝓝 (((k : ℂ) + 1) * twinCorrection 1)) := by
  have hA := tendsto_mul_vonMangoldtSymbol_one
  have hh : Tendsto twinCorrection (𝓝[≠] 1) (𝓝 (twinCorrection 1)) :=
    (continuousAt_twinCorrection (by norm_num)).tendsto.mono_left nhdsWithin_le_nhds
  have hsub : Tendsto (fun s : ℂ => s - 1) (𝓝[≠] 1) (𝓝 0) := by
    have : Tendsto (fun s : ℂ => s - 1) (𝓝 1) (𝓝 (1 - 1)) := (continuous_id.sub continuous_const).tendsto 1
    rw [sub_self] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hT : Tendsto (fun s => (s - 1) * twinSymbol s) (𝓝[≠] 1) (𝓝 1) := by
    have h1 := hA.add (hsub.mul hh)
    rw [zero_mul, add_zero] at h1
    refine h1.congr fun s => ?_
    rw [twinSymbol_eq]
    ring
  induction k with
  | zero =>
    simp only [pow_zero, one_mul, zero_add, Nat.cast_zero, pow_one]
    refine hh.congr fun s => ?_
    rw [twinSymbol_eq]
    ring
  | succ k ih =>
    have hstep := (hT.mul ih).add ((hA.pow (k + 1)).mul hh)
    have hval : (1 : ℂ) * (((k : ℂ) + 1) * twinCorrection 1) + 1 ^ (k + 1) * twinCorrection 1 =
        (((k + 1 : ℕ) : ℂ) + 1) * twinCorrection 1 := by
      push_cast
      ring
    rw [hval] at hstep
    refine hstep.congr fun s => ?_
    have hT' : twinSymbol s = vonMangoldtSymbol s + twinCorrection s := twinSymbol_eq s
    have hexp : twinSymbol s ^ (k + 1 + 1) - vonMangoldtSymbol s ^ (k + 1 + 1) =
        twinSymbol s * (twinSymbol s ^ (k + 1) - vonMangoldtSymbol s ^ (k + 1)) +
          vonMangoldtSymbol s ^ (k + 1) * twinCorrection s := by
      rw [hT']
      ring
    rw [hexp, mul_pow]
    ring

/-- **At a zero nothing separates, at any degree.** -/
theorem tendsto_sub_pow_twinSymbol_at_zero {ρ : ℂ} (hz : riemannZeta ρ = 0) (hρ : 1 / 2 < ρ.re) (k : ℕ) :
    Tendsto (fun s => (s - ρ) ^ k * (twinSymbol s ^ k - vonMangoldtSymbol s ^ k)) (𝓝[≠] ρ) (𝓝 0) := by
  obtain ⟨m, -, hA'⟩ := _root_.RHTower.neg_logDeriv_zeta_zero_residue hz
  have hA : Tendsto (fun s => (s - ρ) * vonMangoldtSymbol s) (𝓝[≠] ρ) (𝓝 (-(m : ℂ))) :=
    hA'.congr fun s => by rw [vonMangoldtSymbol_eq]
  have hh : Tendsto twinCorrection (𝓝[≠] ρ) (𝓝 (twinCorrection ρ)) :=
    (continuousAt_twinCorrection hρ).tendsto.mono_left nhdsWithin_le_nhds
  have hsub : Tendsto (fun s : ℂ => s - ρ) (𝓝[≠] ρ) (𝓝 0) := by
    have : Tendsto (fun s : ℂ => s - ρ) (𝓝 ρ) (𝓝 (ρ - ρ)) := (continuous_id.sub continuous_const).tendsto ρ
    rw [sub_self] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hsh : Tendsto (fun s => (s - ρ) * twinCorrection s) (𝓝[≠] ρ) (𝓝 0) := by
    have h1 := hsub.mul hh
    rwa [zero_mul] at h1
  have hT : Tendsto (fun s => (s - ρ) * twinSymbol s) (𝓝[≠] ρ) (𝓝 (-(m : ℂ))) := by
    have h1 := hA.add hsh
    rw [add_zero] at h1
    refine h1.congr fun s => ?_
    rw [twinSymbol_eq]
    ring
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep := (hT.mul ih).add ((hA.pow k).mul hsh)
    rw [mul_zero, mul_zero, add_zero] at hstep
    refine hstep.congr fun s => ?_
    have hT' : twinSymbol s = vonMangoldtSymbol s + twinCorrection s := twinSymbol_eq s
    have hexp : twinSymbol s ^ (k + 1) - vonMangoldtSymbol s ^ (k + 1) =
        twinSymbol s * (twinSymbol s ^ k - vonMangoldtSymbol s ^ k) +
          vonMangoldtSymbol s ^ k * twinCorrection s := by
      rw [hT']
      ring
    rw [hexp, mul_pow]
    ring

end GaloisForLFunctions.RigidArithmeticOfCuts
