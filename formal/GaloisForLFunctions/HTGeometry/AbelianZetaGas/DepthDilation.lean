import GaloisForLFunctions.HTGeometry.AbelianZetaGas.Response

/-!
# Depth dilation is an exact renormalisation semigroup

The map `δ_d : (p, j) ↦ (p, d·j)` on prime-depth modes multiplies every mode energy by `d`, so
pulling the gas back along `δ_d` is the same as raising the temperature parameter from `σ` to
`d·σ`.  The maps compose, `δ_d ∘ δ_e = δ_{de}`, so `(ℕ_{≥1}, ×)` acts on the gas; and the zeta
ladder restricted to the depth-`dℕ` modes at `σ` is the full ladder at `d·σ`.

This is the measure-theoretic content of (GAS.11); the operator-algebraic clause, the unital
`*`-embedding of the mode algebra, waits on the KMS layer.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Depth dilation of prime-depth modes: the mode of depth `j` at `p` goes to depth `d·j`. -/
def depthDilation (d : ℕ) (m : AbelianZetaMode) : AbelianZetaMode := (m.1, d * (m.2 + 1) - 1)

@[simp] theorem depthDilation_fst (d : ℕ) (m : AbelianZetaMode) :
    (depthDilation d m).1 = m.1 := rfl

theorem depth_depthDilation {d : ℕ} (hd : 1 ≤ d) (m : AbelianZetaMode) :
    AbelianZetaMode.depth (depthDilation d m) = d * AbelianZetaMode.depth m := by
  have hpos : 1 ≤ d * (m.2 + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  simp only [AbelianZetaMode.depth, depthDilation]
  omega

theorem depthDilation_injective {d : ℕ} (hd : 1 ≤ d) :
    Function.Injective (depthDilation d) := by
  intro m m' h
  have h1 : m.1 = m'.1 := by
    have hfst := congrArg Prod.fst h
    simpa using hfst
  have h2 : d * (m.2 + 1) - 1 = d * (m'.2 + 1) - 1 := congrArg Prod.snd h
  have hpos : 1 ≤ d * (m.2 + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hpos' : 1 ≤ d * (m'.2 + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have heq : d * (m.2 + 1) = d * (m'.2 + 1) := by omega
  have hsnd : m.2 = m'.2 := by
    have := Nat.eq_of_mul_eq_mul_left (by omega : 0 < d) heq
    omega
  exact Prod.ext h1 hsnd

/-- **The dilations form a semigroup**: `δ_d ∘ δ_e = δ_{d·e}`. -/
theorem depthDilation_comp {d e : ℕ} (_hd : 1 ≤ d) (he : 1 ≤ e) (m : AbelianZetaMode) :
    depthDilation d (depthDilation e m) = depthDilation (d * e) m := by
  have hpos : 1 ≤ e * (m.2 + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  refine Prod.ext rfl ?_
  simp only [depthDilation]
  have hrw : e * (m.2 + 1) - 1 + 1 = e * (m.2 + 1) := by omega
  rw [hrw, ← Nat.mul_assoc]

namespace AbelianZetaParameters

/-- The dilated temperature parameters: `σ ↦ d·σ`. -/
def depthDilate (θ : AbelianZetaParameters) (d : ℕ) (hd : 1 ≤ d) : AbelianZetaParameters where
  sigma := (d : ℝ) * θ.sigma
  tau := θ.tau
  sigma_pos := by
    have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have := θ.sigma_pos
    nlinarith
  tau_nonneg := θ.tau_nonneg

@[simp] theorem depthDilate_sigma (θ : AbelianZetaParameters) (d : ℕ) (hd : 1 ≤ d) :
    (θ.depthDilate d hd).sigma = (d : ℝ) * θ.sigma := rfl

@[simp] theorem depthDilate_tau (θ : AbelianZetaParameters) (d : ℕ) (hd : 1 ≤ d) :
    (θ.depthDilate d hd).tau = θ.tau := rfl

/-- **(GAS.11), state clause.**  Pulling the gas back along the depth dilation `δ_d` is the same as
dilating the temperature parameter: `φ_σ ∘ ι_d = φ_{dσ}`. -/
theorem ratio_depthDilation (θ : AbelianZetaParameters) {d : ℕ} (hd : 1 ≤ d)
    (m : AbelianZetaMode) :
    θ.ratio (depthDilation d m) = (θ.depthDilate d hd).ratio m := by
  rw [ratio, ratio, exponent, exponent, depth_depthDilation hd m, depthDilate_sigma,
    depthDilate_tau]
  congr 2
  push_cast
  ring

end AbelianZetaParameters

namespace AbelianZetaConvergentParameters

/-- The dilated parameters stay in the convergence chamber. -/
def depthDilate (θ : AbelianZetaConvergentParameters) (d : ℕ) (hd : 1 ≤ d) :
    AbelianZetaConvergentParameters where
  toAbelianZetaParameters := θ.toAbelianZetaParameters.depthDilate d hd
  firstDepth := by
    have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have hσ := θ.sigma_pos
    have hfirst := θ.firstDepth
    have : θ.sigma ≤ (d : ℝ) * θ.sigma := by nlinarith
    simp only [AbelianZetaParameters.depthDilate]
    linarith

/-- **(GAS.11), partition clause.**  The zeta ladder at the dilated temperature is the ladder of
the depth-`dℕ` modes at the original temperature. -/
theorem zetaPartition_depthDilate (θ : AbelianZetaConvergentParameters) {d : ℕ} (hd : 1 ≤ d) :
    (θ.depthDilate d hd).zetaPartition
      = ∏' n : ℕ, riemannZeta ((((d * (n + 1) : ℕ) : ℝ) * θ.sigma + θ.tau : ℝ) : ℂ) := by
  rw [zetaPartition]
  refine tprod_congr fun n => ?_
  congr 2
  simp only [depthDilate, AbelianZetaParameters.depthDilate]
  push_cast
  ring

end AbelianZetaConvergentParameters

end

end GaloisForLFunctions.HTGeometry
