/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GaloisForLFunctions.RHTower.FermiNymanWitnessGermLaws
import GaloisForLFunctions.RHTower.FermiNymanLogMobiusHead
import GaloisForLFunctions.RHTower.FermiNymanDyadicFoldGeometry

/-!
# Pillar XXXI: Witness Germ Origin-Mass Decomposition & Joint Small-`t` Tail + Head Synthesis

This module establishes the third structural pillar addressing **Wall 1**
(`docs/reports/walls-ledger.md`) in the `BiScaleUncertainty` architecture: **coupling the
dual witness origin-mass functional `witnessMass w x = ∫_0^x ‖w(t)‖^2 dt` to the fold-free
kernel `ker P` and the joint small-`t` tail + Chebyshev head decomposition at cutoff `1/(N+1)`**.

## Mathematical Architecture

On the dual side of `L²(0, 1] = ker P ⊕ ℂ · s₀`, the witness space `W = {φ_a}^⊥` controls the
Haar approximation defect via the origin-mass functional `m_w(x) = ∫_0^x ‖w(t)‖^2 dt`
(`RHTower.witnessMass`). Every theorem in this file is **100% unconditional and
hypothesis-free**, formulated directly on bundled `L2FermiWitness` objects and natural-scale
indices `a, b, K, N : ℕ`:

1. **Bundled `L2FermiWitness` & Fold-Free Kernel Witness Pairing (§1):**
   We bundle square-integrable Fermi–Nyman witnesses (`RHTower.IsL2FermiWitness`) into the
   type `L2FermiWitness` (inhabited by `zeroL2FermiWitness`). For every `w : L2FermiWitness`
   and natural scale `a + 1`, the fold-free generator
   `foldFreeFermiGenNat a t = φ_{a+1}(t) + (1 / (2(a+1))) s₀(t) ∈ ker P` pairs with `w`
   solely through the canonical self-similar shadow `s₀`:
   `∫_0^1 foldFreeFermiGenNat a t * conj(w t) = (1 / (2(a+1))) ∫_0^1 s₀(t) * conj(w t)`.
   Consequently, the **scale-balanced kernel difference**
   `scaleBalancedFermiDiff a b t = (a+1) φ_{a+1}(t) - (b+1) φ_{b+1}(t)`
   lies simultaneously in `ker P`, in `s₀^⊥`, and in `W^⊥` (orthogonal to every
   `w : L2FermiWitness`).

2. **Exact Dyadic Shell Decomposition of the Origin Mass `witnessMass` (§2):**
   For every `w : L2FermiWitness` and octave depth `K : ℕ`, the total witness energy
   `witnessMass w 1` splits identically into the small-`t` origin germ mass at scale `2^{-K}`
   plus the finite sum of rescaled top-octave shell energies:
   `witnessMass w 1 = witnessMass w ((1/2)^K) + ∑ j ∈ range K, ∫ t in dyadicShell j, ‖w t‖^2`.

3. **Joint Small-`t` Tail + Bulk Head Witness Duality Bound (§3):**
   For every `w : L2FermiWitness`, cutoff `N : ℕ`, and finite natural-scale generator
   combination `Φ = ∑_j c_j φ_{a_j+1}`, the global Haar witness pairing
   `∫_0^1 h(t) conj(w(t)) dt` equals `∫_0^1 (h(t) - Φ(t)) conj(w(t)) dt` and splits across
   the cutoff `1/(N+1) ∈ (0, 1]` into:
   - the **small-`t` origin tail** on `(0, 1/(N+1)]`, weighted by the witness origin mass
     `witnessMass w (1 / (N + 1))`, and
   - the **bulk head** on `(1/(N+1), 1]`, weighted by the bulk witness mass
     `witnessMass w 1 - witnessMass w (1 / (N + 1))`.

4. **Unconditional Log-Möbius Tail + Chebyshev Head Decomposition & Centered Error Link (§4):**
   For every `N : ℕ` (at shifted cutoff `N + 2 ≥ 2`), `logMobiusFermiErrorEnergy (N + 2)`
   splits unconditionally into the `(0, 1/(N+3)]` tail and the `(1/(N+3), 1]` dyadic Chebyshev
   head `(2ψ(1/(2t)) - ψ(1/t)) / log(N+2)`, where the linear main term cancels identically:
   `2ψ(x/2) - ψ(x) = 2(ψ(x/2) - x/2) - (ψ(x) - x)`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal NNReal
open GaloisForLFunctions.NymanMellin GaloisForLFunctions.HTGeometry
open RHTower

noncomputable section

namespace GaloisForLFunctions.BiScaleUncertainty

/-! ## §1. Bundled `L2FermiWitness` & Scale-Balanced Kernel Orthogonality -/

/-- Bundled measurable square-integrable witness of the alternating Fermi–Nyman system on `(0, 1]`,
packaging a function `toFun : ℝ → ℂ` together with `IsL2FermiWitness toFun` so that all dual
witness theorems are 100% hypothesis-free. -/
structure L2FermiWitness where
  toFun : ℝ → ℂ
  isWitness : IsL2FermiWitness toFun

instance : CoeFun L2FermiWitness (fun _ => ℝ → ℂ) := ⟨L2FermiWitness.toFun⟩

/-- The identically zero function on `ℝ` as the canonical basepoint of `L2FermiWitness`. -/
def zeroL2FermiWitness : L2FermiWitness where
  toFun := fun _ => 0
  isWitness := ⟨measurable_const, by simp, fun _ _ => by simp⟩

instance : Inhabited L2FermiWitness := ⟨zeroL2FermiWitness⟩

@[simp]
theorem zeroL2FermiWitness_apply (t : ℝ) : zeroL2FermiWitness t = 0 := rfl

theorem L2FermiWitness.measurable_toFun (w : L2FermiWitness) : Measurable w :=
  w.isWitness.measurable

theorem L2FermiWitness.integrableOn_normSq (w : L2FermiWitness) :
    IntegrableOn (fun t => ‖w t‖ ^ 2) (Ioc (0 : ℝ) 1) :=
  w.isWitness.sq

theorem L2FermiWitness.integrableOn_toFun (w : L2FermiWitness) :
    IntegrableOn w (Ioc (0 : ℝ) 1) :=
  ((memLp_two_iff_integrable_sq_norm w.measurable_toFun.aestronglyMeasurable).mpr
    w.integrableOn_normSq).integrable (by norm_num)

/-- Every `w : L2FermiWitness` is unconditionally orthogonal to every natural-scale generator
`φ_{a+1}` on `(0, 1]`. -/
theorem L2FermiWitness.integral_fermiNymanGen_nat_mul_conj_eq_zero
    (w : L2FermiWitness) (a : ℕ) :
    ∫ t in Ioc (0 : ℝ) 1,
      fermiNymanGen ((a + 1 : ℕ) : ℝ) t * (starRingEnd ℂ) (w t) = 0 :=
  w.isWitness.orth ((a + 1 : ℕ) : ℝ) (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le a))

/-- The fold-free Fermi–Nyman generator at natural scale `a + 1`:
$$\tilde{\varphi}_{a+1}(t) := \varphi_{a+1}(t) + \frac{1}{2(a+1)} s_0(t) \in \ker P,$$
where $s_0 = \operatorname{selfSimilarExtension}(u \mapsto u^{-1})$. -/
def foldFreeFermiGenNat (a : ℕ) (t : ℝ) : ℂ :=
  fermiNymanGen ((a + 1 : ℕ) : ℝ) t +
    (1 / (2 * ((a + 1 : ℕ) : ℂ))) * selfSimilarExtension (fun u : ℝ => ((u : ℂ))⁻¹) t

theorem measurable_foldFreeFermiGenNat (a : ℕ) :
    Measurable (foldFreeFermiGenNat a) :=
  (measurable_fermiNymanGen _).add
    (measurable_const.mul (measurable_selfSimilarExtension Complex.measurable_ofReal.inv))

theorem integrableOn_normSq_foldFreeFermiGenNat (a : ℕ) :
    IntegrableOn (fun t => ‖foldFreeFermiGenNat a t‖ ^ 2) (Ioc (0 : ℝ) 1) := by
  have h1 : MemLp (fermiNymanGen ((a + 1 : ℕ) : ℝ)) 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (memLp_two_iff_integrable_sq_norm (measurable_fermiNymanGen _).aestronglyMeasurable).mpr
      (integrableOn_normSq_fermiNymanGen _)
  have h2 : MemLp
      (fun t => (1 / (2 * ((a + 1 : ℕ) : ℂ))) * selfSimilarExtension (fun u : ℝ => ((u : ℂ))⁻¹) t) 2
      (volume.restrict (Ioc (0 : ℝ) 1)) :=
    ((memLp_two_iff_integrable_sq_norm
      (measurable_selfSimilarExtension Complex.measurable_ofReal.inv).aestronglyMeasurable).mpr
      integrableOn_normSq_selfSimilarExtension_inv).const_mul _
  exact (memLp_two_iff_integrable_sq_norm (measurable_foldFreeFermiGenNat a).aestronglyMeasurable).mp
    (h1.add h2)

/-- **Unconditional Witness Pairing Against Fold-Free Generators
(`L2FermiWitness.integral_foldFreeFermiGenNat_mul_conj_eq`):**
For EVERY `w : L2FermiWitness` and `a : ℕ` (with **zero hypotheses**!), the inner product of the
fold-free generator $\tilde{\varphi}_{a+1} \in \ker P$ with $w$ reduces purely to its harmonic
multiple of the canonical self-similar shadow pairing $\langle s_0, w \rangle$:
$$\int_0^1 \tilde{\varphi}_{a+1}(t)\,\overline{w(t)}\,dt
  = \frac{1}{2(a+1)} \int_0^1 s_0(t)\,\overline{w(t)}\,dt.$$ -/
theorem L2FermiWitness.integral_foldFreeFermiGenNat_mul_conj_eq
    (w : L2FermiWitness) (a : ℕ) :
    (∫ t in Ioc (0 : ℝ) 1, foldFreeFermiGenNat a t * (starRingEnd ℂ) (w t)) =
      (1 / (2 * ((a + 1 : ℕ) : ℂ))) *
        ∫ t in Ioc (0 : ℝ) 1,
          selfSimilarExtension (fun u : ℝ => ((u : ℂ))⁻¹) t * (starRingEnd ℂ) (w t) := by
  have h1 : IntegrableOn
      (fun t => fermiNymanGen ((a + 1 : ℕ) : ℝ) t * (starRingEnd ℂ) (w t)) (Ioc (0 : ℝ) 1) :=
    integrableOn_mul_conj_of_sq (measurable_fermiNymanGen _) w.measurable_toFun
      (integrableOn_normSq_fermiNymanGen _) w.integrableOn_normSq
  have h2 : IntegrableOn
      (fun t => selfSimilarExtension (fun u : ℝ => ((u : ℂ))⁻¹) t * (starRingEnd ℂ) (w t))
      (Ioc (0 : ℝ) 1) :=
    integrableOn_mul_conj_of_sq (measurable_selfSimilarExtension Complex.measurable_ofReal.inv)
      w.measurable_toFun integrableOn_normSq_selfSimilarExtension_inv w.integrableOn_normSq
  have hsplit : (fun t => foldFreeFermiGenNat a t * (starRingEnd ℂ) (w t)) =
      fun t => fermiNymanGen ((a + 1 : ℕ) : ℝ) t * (starRingEnd ℂ) (w t) +
        (1 / (2 * ((a + 1 : ℕ) : ℂ))) *
          (selfSimilarExtension (fun u : ℝ => ((u : ℂ))⁻¹) t * (starRingEnd ℂ) (w t)) := by
    funext t
    unfold foldFreeFermiGenNat
    ring
  rw [hsplit, integral_add h1 (h2.const_mul _),
    w.integral_fermiNymanGen_nat_mul_conj_eq_zero a, zero_add, integral_const_mul]

/-- The **scale-balanced kernel difference** between natural scales `a + 1` and `b + 1`:
$$\Delta_{a,b}(t) := (a + 1)\,\varphi_{a+1}(t) - (b + 1)\,\varphi_{b+1}(t).$$
Multiplying each generator by its scale index cancels the $-(a+1)^{-1} u^{-1}$ fold shadow
identically, producing a pure generator combination in $\ker P \cap W^\perp \cap s_0^\perp$. -/
def scaleBalancedFermiDiff (a b : ℕ) (t : ℝ) : ℂ :=
  ((a + 1 : ℕ) : ℂ) * fermiNymanGen ((a + 1 : ℕ) : ℝ) t -
    ((b + 1 : ℕ) : ℂ) * fermiNymanGen ((b + 1 : ℕ) : ℝ) t

/-- **Exact Cancellation of the Self-Similar Shadow in `scaleBalancedFermiDiff`:**
For EVERY `a b : ℕ` and `t : ℝ` (with **zero hypotheses**!), the scale-balanced generator
difference coincides identically with the scale-balanced fold-free generator difference:
$$(a + 1)\,\varphi_{a+1}(t) - (b + 1)\,\varphi_{b+1}(t)
  = (a + 1)\,\tilde{\varphi}_{a+1}(t) - (b + 1)\,\tilde{\varphi}_{b+1}(t).$$ -/
theorem scaleBalancedFermiDiff_eq_foldFree_sub (a b : ℕ) (t : ℝ) :
    scaleBalancedFermiDiff a b t =
      ((a + 1 : ℕ) : ℂ) * foldFreeFermiGenNat a t -
        ((b + 1 : ℕ) : ℂ) * foldFreeFermiGenNat b t := by
  unfold scaleBalancedFermiDiff foldFreeFermiGenNat
  have ha : ((a + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero a)
  have hb : ((b + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero b)
  field_simp [ha, hb]
  ring

/-- **Unconditional Double Orthogonality of `scaleBalancedFermiDiff` to Every Witness
(`L2FermiWitness.integral_scaleBalancedFermiDiff_mul_conj_eq_zero`):**
For EVERY `w : L2FermiWitness` and `a b : ℕ` (with **zero hypotheses**!), the scale-balanced
kernel element $\Delta_{a,b} \in \ker P$ is orthogonal to $w$ on $(0, 1]$:
$$\int_0^1 \Delta_{a,b}(t)\,\overline{w(t)}\,dt = 0.$$ -/
theorem L2FermiWitness.integral_scaleBalancedFermiDiff_mul_conj_eq_zero
    (w : L2FermiWitness) (a b : ℕ) :
    ∫ t in Ioc (0 : ℝ) 1, scaleBalancedFermiDiff a b t * (starRingEnd ℂ) (w t) = 0 := by
  have ha : IntegrableOn
      (fun t => fermiNymanGen ((a + 1 : ℕ) : ℝ) t * (starRingEnd ℂ) (w t)) (Ioc (0 : ℝ) 1) :=
    integrableOn_mul_conj_of_sq (measurable_fermiNymanGen _) w.measurable_toFun
      (integrableOn_normSq_fermiNymanGen _) w.integrableOn_normSq
  have hb : IntegrableOn
      (fun t => fermiNymanGen ((b + 1 : ℕ) : ℝ) t * (starRingEnd ℂ) (w t)) (Ioc (0 : ℝ) 1) :=
    integrableOn_mul_conj_of_sq (measurable_fermiNymanGen _) w.measurable_toFun
      (integrableOn_normSq_fermiNymanGen _) w.integrableOn_normSq
  have hsplit : (fun t => scaleBalancedFermiDiff a b t * (starRingEnd ℂ) (w t)) =
      fun t => ((a + 1 : ℕ) : ℂ) * (fermiNymanGen ((a + 1 : ℕ) : ℝ) t * (starRingEnd ℂ) (w t)) -
        ((b + 1 : ℕ) : ℂ) * (fermiNymanGen ((b + 1 : ℕ) : ℝ) t * (starRingEnd ℂ) (w t)) := by
    funext t
    unfold scaleBalancedFermiDiff
    ring
  rw [hsplit, integral_sub (ha.const_mul _) (hb.const_mul _),
    integral_const_mul, integral_const_mul,
    w.integral_fermiNymanGen_nat_mul_conj_eq_zero a,
    w.integral_fermiNymanGen_nat_mul_conj_eq_zero b, mul_zero, mul_zero, sub_self]

/-- **Unconditional Orthogonality of `scaleBalancedFermiDiff` to the Self-Similar Shadow $s_0$:**
For EVERY `a b : ℕ` (with **zero hypotheses**!), the scale-balanced kernel difference
$\Delta_{a,b}$ is orthogonal to $\operatorname{selfSimilarExtension}(u \mapsto u^{-1})$ on $(0, 1]$:
$$\int_0^1 \Delta_{a,b}(t)\,\overline{s_0(t)}\,dt = 0.$$ -/
theorem integral_scaleBalancedFermiDiff_mul_conj_selfSimilarExtension_inv_eq_zero (a b : ℕ) :
    ∫ t in Ioc (0 : ℝ) 1,
      scaleBalancedFermiDiff a b t *
        (starRingEnd ℂ) (selfSimilarExtension (fun u : ℝ => ((u : ℂ))⁻¹) t) = 0 := by
  set s0 : ℝ → ℂ := selfSimilarExtension (fun u : ℝ => ((u : ℂ))⁻¹)
  have hs0_meas : Measurable s0 := measurable_selfSimilarExtension Complex.measurable_ofReal.inv
  have hs0_sq : IntegrableOn (fun t => ‖s0 t‖ ^ 2) (Ioc (0 : ℝ) 1) :=
    integrableOn_normSq_selfSimilarExtension_inv
  have hs0_ss : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) 1)), s0 (t / 2) = s0 t :=
    ae_selfSimilar_selfSimilarExtension (fun u : ℝ => ((u : ℂ))⁻¹)
  have ha1 : (1 : ℝ) ≤ ((a + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le a)
  have hb1 : (1 : ℝ) ≤ ((b + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le b)
  have ha0 : ((a + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero a)
  have hb0 : ((b + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero b)
  have hIntA : IntegrableOn
      (fun t => fermiNymanGen ((a + 1 : ℕ) : ℝ) t * (starRingEnd ℂ) (s0 t))
      (Ioc (0 : ℝ) 1) :=
    integrableOn_mul_conj_of_sq (measurable_fermiNymanGen _) hs0_meas
      (integrableOn_normSq_fermiNymanGen _) hs0_sq
  have hIntB : IntegrableOn
      (fun t => fermiNymanGen ((b + 1 : ℕ) : ℝ) t * (starRingEnd ℂ) (s0 t))
      (Ioc (0 : ℝ) 1) :=
    integrableOn_mul_conj_of_sq (measurable_fermiNymanGen _) hs0_meas
      (integrableOn_normSq_fermiNymanGen _) hs0_sq
  have hsplit : (fun t => scaleBalancedFermiDiff a b t * (starRingEnd ℂ) (s0 t)) =
      fun t => ((a + 1 : ℕ) : ℂ) *
          (fermiNymanGen ((a + 1 : ℕ) : ℝ) t * (starRingEnd ℂ) (s0 t)) -
        ((b + 1 : ℕ) : ℂ) *
          (fermiNymanGen ((b + 1 : ℕ) : ℝ) t * (starRingEnd ℂ) (s0 t)) := by
    funext t
    unfold scaleBalancedFermiDiff
    ring
  rw [hsplit, integral_sub (hIntA.const_mul _) (hIntB.const_mul _),
    integral_const_mul, integral_const_mul,
    integral_fermiNymanGen_mul_conj_of_ae_selfSimilar hs0_meas hs0_sq hs0_ss ha1,
    integral_fermiNymanGen_mul_conj_of_ae_selfSimilar hs0_meas hs0_sq hs0_ss hb1]
  push_cast
  field_simp [ha0, hb0]
  ring

/-! ## §2. Exact Dyadic Shell Decomposition of the Origin Mass `witnessMass` -/

/-- **Single-Octave Recurrence for `witnessMass` (`L2FermiWitness.witnessMass_pow_half_eq_succ_add_shell`):**
For EVERY `w : L2FermiWitness` and octave `j : ℕ` (with **zero hypotheses**!), the origin mass at
scale $2^{-j}$ splits into the origin mass at scale $2^{-(j+1)}$ plus the energy on the $j$-th
dyadic shell $(2^{-(j+1)}, 2^{-j}]$:
$$\operatorname{witnessMass}\!\left(w, \frac{1}{2^j}\right)
  = \operatorname{witnessMass}\!\left(w, \frac{1}{2^{j+1}}\right)
    + \int_{t \in \mathrm{dyadicShell}\,j} \|w(t)\|^2\,dt.$$ -/
theorem L2FermiWitness.witnessMass_pow_half_eq_succ_add_shell
    (w : L2FermiWitness) (j : ℕ) :
    witnessMass w ((1 / 2 : ℝ) ^ j) =
      witnessMass w ((1 / 2 : ℝ) ^ (j + 1)) +
        ∫ t in dyadicShell j, ‖w t‖ ^ 2 := by
  have hc0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (j + 1) := pow_nonneg (by norm_num) (j + 1)
  have hc1 : (1 / 2 : ℝ) ^ (j + 1) ≤ (1 / 2 : ℝ) ^ j := (half_pow_succ_lt j).le
  have hj1 : (1 / 2 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hleft : IntegrableOn (fun t => ‖w t‖ ^ 2) (Ioc (0 : ℝ) ((1 / 2 : ℝ) ^ (j + 1))) :=
    w.integrableOn_normSq.mono_set (Ioc_subset_Ioc_right (hc1.trans hj1))
  have hright : IntegrableOn (fun t => ‖w t‖ ^ 2) (dyadicShell j) :=
    w.integrableOn_normSq.mono_set (Ioc_subset_Ioc hc0 hj1)
  unfold witnessMass dyadicShell
  rw [← Ioc_union_Ioc_eq_Ioc hc0 hc1,
    setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc hleft hright]

/-- **Unconditional Multi-Octave Dyadic Shell Decomposition of Total Witness Energy
(`L2FermiWitness.witnessMass_one_eq_pow_half_add_sum_dyadicShell`):**
For EVERY `w : L2FermiWitness` and octave depth `K : ℕ` (with **zero hypotheses**!), the total
witness $L^2$ energy `witnessMass w 1` decomposes identically into the origin germ mass below
$2^{-K}$ plus the finite sum of the first $K$ dyadic shell energies:
$$\operatorname{witnessMass}(w, 1)
  = \operatorname{witnessMass}\!\left(w, \frac{1}{2^K}\right)
    + \sum_{j \in \mathrm{range}\,K} \int_{t \in \mathrm{dyadicShell}\,j} \|w(t)\|^2\,dt.$$ -/
theorem L2FermiWitness.witnessMass_one_eq_pow_half_add_sum_dyadicShell
    (w : L2FermiWitness) (K : ℕ) :
    witnessMass w 1 =
      witnessMass w ((1 / 2 : ℝ) ^ K) +
        ∑ j ∈ Finset.range K, ∫ t in dyadicShell j, ‖w t‖ ^ 2 := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [ih, w.witnessMass_pow_half_eq_succ_add_shell K, Finset.sum_range_succ]
    ring

/-- **Unconditional Origin-Mass Shell Complement Law
(`L2FermiWitness.witnessMass_pow_half_eq_sub_sum_dyadicShell`):**
For EVERY `w : L2FermiWitness` and octave depth `K : ℕ` (with **zero hypotheses**!), the small-$t$
origin mass at scale $2^{-K}$ equals the total witness energy minus the bulk energy captured by
the top $K$ dyadic shells:
$$\operatorname{witnessMass}\!\left(w, \frac{1}{2^K}\right)
  = \operatorname{witnessMass}(w, 1)
    - \sum_{j \in \mathrm{range}\,K} \int_{t \in \mathrm{dyadicShell}\,j} \|w(t)\|^2\,dt.$$ -/
theorem L2FermiWitness.witnessMass_pow_half_eq_sub_sum_dyadicShell
    (w : L2FermiWitness) (K : ℕ) :
    witnessMass w ((1 / 2 : ℝ) ^ K) =
      witnessMass w 1 -
        ∑ j ∈ Finset.range K, ∫ t in dyadicShell j, ‖w t‖ ^ 2 := by
  have h := w.witnessMass_one_eq_pow_half_add_sum_dyadicShell K
  linarith

/-- **Unconditional Rescaled Top-Octave Form of the Dyadic Shell Sum:**
For EVERY `w : L2FermiWitness` and octave depth `K : ℕ` (with **zero hypotheses**!),
$$\operatorname{witnessMass}(w, 1)
  = \operatorname{witnessMass}\!\left(w, \frac{1}{2^K}\right)
    + \sum_{j \in \mathrm{range}\,K} \frac{1}{2^j} \int_{1/2}^1 \bigl\|w(2^{-j} u)\bigr\|^2\,du.$$ -/
theorem L2FermiWitness.witnessMass_one_eq_pow_half_add_sum_top_octave
    (w : L2FermiWitness) (K : ℕ) :
    witnessMass w 1 =
      witnessMass w ((1 / 2 : ℝ) ^ K) +
        ∑ j ∈ Finset.range K,
          (1 / 2 : ℝ) ^ j * ∫ u in Ioc (1 / 2 : ℝ) 1, ‖w ((1 / 2 : ℝ) ^ j * u)‖ ^ 2 := by
  rw [w.witnessMass_one_eq_pow_half_add_sum_dyadicShell K]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [setIntegral_dyadicShell_eq (fun t => ‖w t‖ ^ 2) j, smul_eq_mul]

/-! ## §3. Joint Small-`t` Tail + Bulk Head Witness Duality Bound at Cutoff `1/(N+1)` -/

/-- A finite linear combination of natural-scale Fermi–Nyman generators $\varphi_{a_j+1}$:
$$\Phi_{c,a}(t) := \sum_{j : \mathrm{Fin}\,m} c_j\,\varphi_{a_j+1}(t).$$ -/
def natScaleFermiComb {m : ℕ} (c : Fin m → ℂ) (a : Fin m → ℕ) (t : ℝ) : ℂ :=
  fermiNymanCombination c (fun j => ((a j + 1 : ℕ) : ℝ)) t

theorem measurable_natScaleFermiComb {m : ℕ} (c : Fin m → ℂ) (a : Fin m → ℕ) :
    Measurable (natScaleFermiComb c a) :=
  measurable_fermiNymanCombination c (fun j => ((a j + 1 : ℕ) : ℝ))

theorem integrableOn_normSq_natScaleFermiComb {m : ℕ} (c : Fin m → ℂ) (a : Fin m → ℕ) :
    IntegrableOn (fun t => ‖natScaleFermiComb c a t‖ ^ 2) (Ioc (0 : ℝ) 1) :=
  integrableOn_normSq_fermiNymanCombination c (fun j => ((a j + 1 : ℕ) : ℝ))

/-- Every `w : L2FermiWitness` is unconditionally orthogonal to every finite natural-scale
generator combination `natScaleFermiComb c a` on `(0, 1]`. -/
theorem L2FermiWitness.integral_natScaleFermiComb_mul_conj_eq_zero
    (w : L2FermiWitness) {m : ℕ} (c : Fin m → ℂ) (a : Fin m → ℕ) :
    ∫ t in Ioc (0 : ℝ) 1, natScaleFermiComb c a t * (starRingEnd ℂ) (w t) = 0 := by
  have hcomb : (fun t => natScaleFermiComb c a t * (starRingEnd ℂ) (w t)) =
      fun t => ∑ j : Fin m,
        c j * (fermiNymanGen ((a j + 1 : ℕ) : ℝ) t * (starRingEnd ℂ) (w t)) := by
    funext t
    unfold natScaleFermiComb fermiNymanCombination
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hcomb, integral_finsetSum _ (fun j _ =>
    (integrableOn_mul_conj_of_sq (measurable_fermiNymanGen _) w.measurable_toFun
      (integrableOn_normSq_fermiNymanGen _) w.integrableOn_normSq).const_mul _)]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [integral_const_mul, w.integral_fermiNymanGen_nat_mul_conj_eq_zero (a j), mul_zero]

/-- **Unconditional Witness Invariance Under Generator Subtraction
(`L2FermiWitness.integral_dyadicHaar_sub_natScaleFermiComb_mul_conj_eq`):**
For EVERY `w : L2FermiWitness` and EVERY finite generator combination `natScaleFermiComb c a`
(with **zero hypotheses**!), the global pairing of `dyadicHaar` against `w` equals the pairing of
the residual `dyadicHaar - natScaleFermiComb c a` against `w`:
$$\int_0^1 h(t)\,\overline{w(t)}\,dt
  = \int_0^1 \bigl(h(t) - \Phi_{c,a}(t)\bigr)\,\overline{w(t)}\,dt.$$ -/
theorem L2FermiWitness.integral_dyadicHaar_sub_natScaleFermiComb_mul_conj_eq
    (w : L2FermiWitness) {m : ℕ} (c : Fin m → ℂ) (a : Fin m → ℕ) :
    (∫ t in Ioc (0 : ℝ) 1, dyadicHaar t * (starRingEnd ℂ) (w t)) =
      ∫ t in Ioc (0 : ℝ) 1,
        (dyadicHaar t - natScaleFermiComb c a t) * (starRingEnd ℂ) (w t) := by
  have h1 : IntegrableOn (fun t => dyadicHaar t * (starRingEnd ℂ) (w t)) (Ioc (0 : ℝ) 1) :=
    integrableOn_mul_conj_of_sq measurable_dyadicHaar w.measurable_toFun
      integrableOn_normSq_dyadicHaar w.integrableOn_normSq
  have h2 : IntegrableOn (fun t => natScaleFermiComb c a t * (starRingEnd ℂ) (w t))
      (Ioc (0 : ℝ) 1) :=
    integrableOn_mul_conj_of_sq (measurable_natScaleFermiComb c a) w.measurable_toFun
      (integrableOn_normSq_natScaleFermiComb c a) w.integrableOn_normSq
  have hsplit : (fun t => (dyadicHaar t - natScaleFermiComb c a t) * (starRingEnd ℂ) (w t)) =
      fun t => dyadicHaar t * (starRingEnd ℂ) (w t) -
        natScaleFermiComb c a t * (starRingEnd ℂ) (w t) := by
    funext t; ring
  rw [hsplit, integral_sub h1 h2, w.integral_natScaleFermiComb_mul_conj_eq_zero c a, sub_zero]

/-- **Unconditional Joint Small-`t` Tail + Bulk Head Split of the Witness Pairing at `1/(N+1)`:**
For EVERY `w : L2FermiWitness`, cutoff `N : ℕ`, and finite generator combination `c, a` (with
**zero hypotheses**!), the Haar witness pairing splits across `1 / (N + 1) ∈ (0, 1]` into the
origin tail pairing on `(0, 1/(N+1)]` plus the bulk head pairing on `(1/(N+1), 1]`:
$$\int_0^1 h(t)\,\overline{w(t)}\,dt
  = \int_0^{1/(N+1)} \bigl(h(t) - \Phi_{c,a}(t)\bigr)\overline{w(t)}\,dt
    + \int_{1/(N+1)}^1 \bigl(h(t) - \Phi_{c,a}(t)\bigr)\overline{w(t)}\,dt.$$ -/
theorem L2FermiWitness.integral_dyadicHaar_mul_conj_eq_tail_add_head
    (w : L2FermiWitness) (N : ℕ) {m : ℕ} (c : Fin m → ℂ) (a : Fin m → ℕ) :
    (∫ t in Ioc (0 : ℝ) 1, dyadicHaar t * (starRingEnd ℂ) (w t)) =
      (∫ t in Ioc (0 : ℝ) (1 / ((N : ℝ) + 1)),
        (dyadicHaar t - natScaleFermiComb c a t) * (starRingEnd ℂ) (w t)) +
      (∫ t in Ioc (1 / ((N : ℝ) + 1)) 1,
        (dyadicHaar t - natScaleFermiComb c a t) * (starRingEnd ℂ) (w t)) := by
  rw [w.integral_dyadicHaar_sub_natScaleFermiComb_mul_conj_eq c a]
  have hc0 : (0 : ℝ) ≤ 1 / ((N : ℝ) + 1) := by positivity
  have hc1 : 1 / ((N : ℝ) + 1) ≤ 1 :=
    (div_le_one (by positivity)).mpr (le_add_of_nonneg_left (Nat.cast_nonneg N))
  have hint : IntegrableOn
      (fun t => (dyadicHaar t - natScaleFermiComb c a t) * (starRingEnd ℂ) (w t))
      (Ioc (0 : ℝ) 1) :=
    integrableOn_mul_conj_of_sq
      (measurable_dyadicHaar.sub (measurable_natScaleFermiComb c a)) w.measurable_toFun
      (integrableOn_normSq_sub measurable_dyadicHaar (measurable_natScaleFermiComb c a)
        integrableOn_normSq_dyadicHaar (integrableOn_normSq_natScaleFermiComb c a))
      w.integrableOn_normSq
  rw [← Ioc_union_Ioc_eq_Ioc hc0 hc1,
    setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
      (hint.mono_set (Ioc_subset_Ioc le_rfl hc1))
      (hint.mono_set (Ioc_subset_Ioc hc0 le_rfl))]

/-- **Unconditional Origin-Mass Cauchy–Schwarz Bound on the Small-`t` Tail Pairing:**
For EVERY `w : L2FermiWitness`, cutoff `N : ℕ`, and generator combination `c, a` (with **zero
hypotheses**!), the squared modulus of the small-$t$ tail pairing on $(0, 1/(N+1)]$ is bounded
above by the witness origin mass `witnessMass w (1 / (N + 1))` times the small-$t$ tail energy:
$$\left\|\int_0^{1/(N+1)} \bigl(h(t) - \Phi_{c,a}(t)\bigr)\overline{w(t)}\,dt\right\|^2
  \le \operatorname{witnessMass}\!\left(w, \frac{1}{N+1}\right)
      \int_0^{1/(N+1)} \bigl\|h(t) - \Phi_{c,a}(t)\bigr\|^2\,dt.$$ -/
theorem L2FermiWitness.norm_sq_tail_pairing_le_witnessMass_mul_tail_energy
    (w : L2FermiWitness) (N : ℕ) {m : ℕ} (c : Fin m → ℂ) (a : Fin m → ℕ) :
    ‖∫ t in Ioc (0 : ℝ) (1 / ((N : ℝ) + 1)),
      (dyadicHaar t - natScaleFermiComb c a t) * (starRingEnd ℂ) (w t)‖ ^ 2 ≤
      witnessMass w (1 / ((N : ℝ) + 1)) *
        ∫ t in Ioc (0 : ℝ) (1 / ((N : ℝ) + 1)),
          ‖dyadicHaar t - natScaleFermiComb c a t‖ ^ 2 := by
  set S : Set ℝ := Ioc (0 : ℝ) (1 / ((N : ℝ) + 1))
  set g : ℝ → ℂ := fun t => dyadicHaar t - natScaleFermiComb c a t
  have hc1 : 1 / ((N : ℝ) + 1) ≤ 1 :=
    (div_le_one (by positivity)).mpr (le_add_of_nonneg_left (Nat.cast_nonneg N))
  have hg_meas : Measurable g := measurable_dyadicHaar.sub (measurable_natScaleFermiComb c a)
  have hg2 : IntegrableOn (fun t => ‖g t‖ ^ 2) S :=
    (integrableOn_normSq_sub measurable_dyadicHaar (measurable_natScaleFermiComb c a)
      integrableOn_normSq_dyadicHaar (integrableOn_normSq_natScaleFermiComb c a)).mono_set
      (Ioc_subset_Ioc le_rfl hc1)
  have hw2 : IntegrableOn (fun t => ‖w t‖ ^ 2) S :=
    w.integrableOn_normSq.mono_set (Ioc_subset_Ioc le_rfl hc1)
  have h1 : ‖∫ t in S, g t * (starRingEnd ℂ) (w t)‖ ≤ ∫ t in S, ‖g t‖ * ‖w t‖ := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [norm_mul, Complex.norm_conj]
  have h2 := sq_integral_mul_le (μ := volume.restrict S) (f := fun t => ‖g t‖)
    (g := fun t => ‖w t‖) hg_meas.aestronglyMeasurable.norm
    w.measurable_toFun.aestronglyMeasurable.norm hg2 hw2
  calc ‖∫ t in S, g t * (starRingEnd ℂ) (w t)‖ ^ 2
      ≤ (∫ t in S, ‖g t‖ * ‖w t‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (∫ t in S, ‖g t‖ ^ 2) * ∫ t in S, ‖w t‖ ^ 2 := h2
    _ = witnessMass w (1 / ((N : ℝ) + 1)) * ∫ t in S, ‖g t‖ ^ 2 := by
        unfold witnessMass S
        ring

/-- **Unconditional Joint Small-`t` Tail + Bulk Head Witness Duality Inequality
(`L2FermiWitness.norm_sq_dyadicHaar_pairing_le_tail_add_head`):**
For EVERY `w : L2FermiWitness`, cutoff `N : ℕ`, and generator combination `c, a` (with **zero
hypotheses**!), the global Haar witness pairing is bounded above jointly by the origin mass at
`1/(N+1)` times the small-`t` tail energy plus the bulk witness mass times the head energy:
$$\left\|\int_0^1 h(t)\,\overline{w(t)}\,dt\right\|^2
  \le 2\,\operatorname{witnessMass}\!\left(w, \frac{1}{N+1}\right)
      \int_0^{1/(N+1)} \bigl\|h(t) - \Phi_{c,a}(t)\bigr\|^2\,dt
    + 2\left(\int_{1/(N+1)}^1 \|w(t)\|^2\,dt\right)
      \int_{1/(N+1)}^1 \bigl\|h(t) - \Phi_{c,a}(t)\bigr\|^2\,dt.$$ -/
theorem L2FermiWitness.norm_sq_dyadicHaar_pairing_le_tail_add_head
    (w : L2FermiWitness) (N : ℕ) {m : ℕ} (c : Fin m → ℂ) (a : Fin m → ℕ) :
    ‖∫ t in Ioc (0 : ℝ) 1, dyadicHaar t * (starRingEnd ℂ) (w t)‖ ^ 2 ≤
      2 * (witnessMass w (1 / ((N : ℝ) + 1)) *
        ∫ t in Ioc (0 : ℝ) (1 / ((N : ℝ) + 1)),
          ‖dyadicHaar t - natScaleFermiComb c a t‖ ^ 2) +
      2 * ((∫ t in Ioc (1 / ((N : ℝ) + 1)) 1, ‖w t‖ ^ 2) *
        ∫ t in Ioc (1 / ((N : ℝ) + 1)) 1,
          ‖dyadicHaar t - natScaleFermiComb c a t‖ ^ 2) := by
  rw [w.integral_dyadicHaar_mul_conj_eq_tail_add_head N c a]
  set I_tail := ∫ t in Ioc (0 : ℝ) (1 / ((N : ℝ) + 1)),
    (dyadicHaar t - natScaleFermiComb c a t) * (starRingEnd ℂ) (w t)
  set I_head := ∫ t in Ioc (1 / ((N : ℝ) + 1)) 1,
    (dyadicHaar t - natScaleFermiComb c a t) * (starRingEnd ℂ) (w t)
  have htri : ‖I_tail + I_head‖ ^ 2 ≤ 2 * ‖I_tail‖ ^ 2 + 2 * ‖I_head‖ ^ 2 := by
    have h1 : ‖I_tail + I_head‖ ≤ ‖I_tail‖ + ‖I_head‖ := norm_add_le _ _
    have h2 : ‖I_tail + I_head‖ ^ 2 ≤ (‖I_tail‖ + ‖I_head‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [sq_nonneg (‖I_tail‖ - ‖I_head‖)]
  have htail := w.norm_sq_tail_pairing_le_witnessMass_mul_tail_energy N c a
  set S_head : Set ℝ := Ioc (1 / ((N : ℝ) + 1)) 1
  set g : ℝ → ℂ := fun t => dyadicHaar t - natScaleFermiComb c a t
  have hc0 : (0 : ℝ) ≤ 1 / ((N : ℝ) + 1) := by positivity
  have hg_meas : Measurable g := measurable_dyadicHaar.sub (measurable_natScaleFermiComb c a)
  have hg2 : IntegrableOn (fun t => ‖g t‖ ^ 2) S_head :=
    (integrableOn_normSq_sub measurable_dyadicHaar (measurable_natScaleFermiComb c a)
      integrableOn_normSq_dyadicHaar (integrableOn_normSq_natScaleFermiComb c a)).mono_set
      (Ioc_subset_Ioc hc0 le_rfl)
  have hw2 : IntegrableOn (fun t => ‖w t‖ ^ 2) S_head :=
    w.integrableOn_normSq.mono_set (Ioc_subset_Ioc hc0 le_rfl)
  have hhead : ‖I_head‖ ^ 2 ≤ (∫ t in S_head, ‖w t‖ ^ 2) * ∫ t in S_head, ‖g t‖ ^ 2 := by
    have h1 : ‖∫ t in S_head, g t * (starRingEnd ℂ) (w t)‖ ≤ ∫ t in S_head, ‖g t‖ * ‖w t‖ := by
      refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      simp only [norm_mul, Complex.norm_conj]
    have h2 := sq_integral_mul_le (μ := volume.restrict S_head) (f := fun t => ‖g t‖)
      (g := fun t => ‖w t‖) hg_meas.aestronglyMeasurable.norm
      w.measurable_toFun.aestronglyMeasurable.norm hg2 hw2
    calc ‖I_head‖ ^ 2
        ≤ (∫ t in S_head, ‖g t‖ * ‖w t‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ (∫ t in S_head, ‖g t‖ ^ 2) * ∫ t in S_head, ‖w t‖ ^ 2 := h2
      _ = (∫ t in S_head, ‖w t‖ ^ 2) * ∫ t in S_head, ‖g t‖ ^ 2 := mul_comm _ _
  linarith

/-! ## §4. Unconditional Log-Möbius Tail + Chebyshev Head Synthesis & Centered Error Link -/

/-- **Unconditional Tail + Chebyshev Head Decomposition of `logMobiusFermiErrorEnergy (N + 2)`:**
For EVERY `N : ℕ` (with **zero hypotheses**!), at cutoff $N + 2 \ge 2$, the total $L^2(0,1]$
error energy of the logarithmically smoothed Möbius–Fermi approximant splits identically into the
unresolved small-$t$ tail on $(0, 1/(N+3)]$ and the normalized Wall 1 dyadic Chebyshev head energy
on $(1/(N+3), 1]$:
$$\operatorname{logMobiusFermiErrorEnergy}(N + 2)
  = \int_0^{1/(N+3)} \bigl\|h(t) - \operatorname{logMobiusFermiApprox}(N + 2, t)\bigr\|^2\,dt
    + \frac{1}{(\log(N+2))^2}
      \int_{1/(N+3)}^1 \bigl(2\psi(1/(2t)) - \psi(1/t)\bigr)^2\,dt.$$ -/
theorem logMobiusFermiErrorEnergy_succ_succ_eq (N : ℕ) :
    logMobiusFermiErrorEnergy (N + 2) =
      (∫ t in Ioc (0 : ℝ) (1 / (((N + 2 : ℕ) : ℝ) + 1)),
        ‖dyadicHaar t - logMobiusFermiApprox (N + 2) t‖ ^ 2) +
      (1 / Real.log ((N + 2 : ℕ) : ℝ) ^ 2) *
        ∫ t in Ioc (1 / (((N + 2 : ℕ) : ℝ) + 1)) 1,
          (2 * Chebyshev.psi (1 / (2 * t)) - Chebyshev.psi (1 / t)) ^ 2 :=
  logMobiusFermiErrorEnergy_decomposition (N + 2) (by omega)

/-- **Unconditional Linear-Drift Cancellation in the Wall 1 Dyadic Chebyshev Head
(`dyadic_chebyshev_head_eq_centered_diff`):**
For EVERY `x : ℝ` (with **zero hypotheses**!), the Wall 1 dyadic Chebyshev difference
$2\psi(x/2) - \psi(x)$ equals the dyadic difference of the centered Chebyshev remainder
$\tilde{\psi}(u) = \psi(u) - u$, because the linear PNT drift $2(x/2) - x = 0$ cancels
identically across the dyadic step:
$$2\psi(x / 2) - \psi(x) = 2\bigl(\psi(x / 2) - x / 2\bigr) - \bigl(\psi(x) - x\bigr).$$ -/
theorem dyadic_chebyshev_head_eq_centered_diff (x : ℝ) :
    2 * Chebyshev.psi (x / 2) - Chebyshev.psi x =
      2 * (Chebyshev.psi (x / 2) - x / 2) - (Chebyshev.psi x - x) := by
  ring

/-- **Unconditional Pointwise Quadratic Upper Bound on the Wall 1 Dyadic Chebyshev Head
(`dyadic_chebyshev_head_sq_le_centered_sq`):**
For EVERY `x : ℝ` (with **zero hypotheses**!), the squared dyadic Chebyshev difference is bounded
from above by the sum of the half-scale and full-scale centered Chebyshev squares:
$$\bigl(2\psi(x / 2) - \psi(x)\bigr)^2
  \le 8\bigl(\psi(x / 2) - x / 2\bigr)^2 + 2\bigl(\psi(x) - x\bigr)^2.$$ -/
theorem dyadic_chebyshev_head_sq_le_centered_sq (x : ℝ) :
    (2 * Chebyshev.psi (x / 2) - Chebyshev.psi x) ^ 2 ≤
      8 * (Chebyshev.psi (x / 2) - x / 2) ^ 2 + 2 * (Chebyshev.psi x - x) ^ 2 := by
  rw [dyadic_chebyshev_head_eq_centered_diff x]
  nlinarith [sq_nonneg (2 * (Chebyshev.psi (x / 2) - x / 2) + (Chebyshev.psi x - x))]

/-- **Unconditional Upper Bound on the Log-Möbius Error Energy via Centered Chebyshev Remainders
(`logMobiusFermiErrorEnergy_succ_succ_le_tail_add_centered_chebyshev`):**
For EVERY `N : ℕ` (with **zero hypotheses**!), `logMobiusFermiErrorEnergy (N + 2)` is bounded
from above by the small-$t$ tail energy plus the centered Chebyshev remainder integrals at
scales $1/(2t)$ and $1/t$:
$$\operatorname{logMobiusFermiErrorEnergy}(N + 2)
  \le \int_0^{1/(N+3)} \bigl\|h(t) - \operatorname{logMobiusFermiApprox}(N + 2, t)\bigr\|^2\,dt
    + \frac{1}{(\log(N+2))^2}
      \int_{1/(N+3)}^1 \Bigl(8\bigl(\psi(1/(2t)) - 1/(2t)\bigr)^2
        + 2\bigl(\psi(1/t) - 1/t\bigr)^2\Bigr)\,dt.$$ -/
theorem logMobiusFermiErrorEnergy_succ_succ_le_tail_add_centered_chebyshev (N : ℕ) :
    logMobiusFermiErrorEnergy (N + 2) ≤
      (∫ t in Ioc (0 : ℝ) (1 / (((N + 2 : ℕ) : ℝ) + 1)),
        ‖dyadicHaar t - logMobiusFermiApprox (N + 2) t‖ ^ 2) +
      (1 / Real.log ((N + 2 : ℕ) : ℝ) ^ 2) *
        ∫ t in Ioc (1 / (((N + 2 : ℕ) : ℝ) + 1)) 1,
          (8 * (Chebyshev.psi (1 / (2 * t)) - 1 / (2 * t)) ^ 2 +
            2 * (Chebyshev.psi (1 / t) - 1 / t) ^ 2) := by
  rw [logMobiusFermiErrorEnergy_succ_succ_eq N]
  have hlog : (0 : ℝ) ≤ 1 / Real.log ((N + 2 : ℕ) : ℝ) ^ 2 := by positivity
  refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ hlog)
  set S : Set ℝ := Ioc (1 / (((N + 2 : ℕ) : ℝ) + 1)) 1
  have hcut : (0 : ℝ) < 1 / (((N + 2 : ℕ) : ℝ) + 1) := by positivity
  have hmeas_psi : Measurable Chebyshev.psi := by
    have hmono : Monotone Chebyshev.psi := fun a b hab => Chebyshev.psi_mono hab
    exact hmono.measurable
  have hInt : IntegrableOn
      (fun t : ℝ => 8 * (Chebyshev.psi (1 / (2 * t)) - 1 / (2 * t)) ^ 2 +
        2 * (Chebyshev.psi (1 / t) - 1 / t) ^ 2) S := by
    refine Measure.integrableOn_of_bounded
      (M := 8 * (Chebyshev.psi (((N + 2 : ℕ) : ℝ) + 1) + (((N + 2 : ℕ) : ℝ) + 1)) ^ 2 +
        2 * (Chebyshev.psi (((N + 2 : ℕ) : ℝ) + 1) + (((N + 2 : ℕ) : ℝ) + 1)) ^ 2)
      measure_Ioc_lt_top.ne ?_ ?_
    · have hm1 : Measurable (fun t : ℝ => Chebyshev.psi (1 / (2 * t)) - 1 / (2 * t)) :=
        (hmeas_psi.comp (measurable_const.div (measurable_const.mul measurable_id))).sub
          (measurable_const.div (measurable_const.mul measurable_id))
      have hm2 : Measurable (fun t : ℝ => Chebyshev.psi (1 / t) - 1 / t) :=
        (hmeas_psi.comp (measurable_const.div measurable_id)).sub
          (measurable_const.div measurable_id)
      exact ((measurable_const.mul (hm1.pow_const 2)).add
        (measurable_const.mul (hm2.pow_const 2))).aestronglyMeasurable
    · rw [ae_restrict_iff' measurableSet_Ioc]
      refine Eventually.of_forall fun t ht => ?_
      have ht0 : 0 < t := lt_trans hcut ht.1
      have h1t : 1 / t ≤ ((N + 2 : ℕ) : ℝ) + 1 := by
        rw [div_le_iff₀ ht0]
        have h := (div_lt_iff₀ (by positivity : (0 : ℝ) < ((N + 2 : ℕ) : ℝ) + 1)).mp ht.1
        linarith
      have h2t : 1 / (2 * t) ≤ ((N + 2 : ℕ) : ℝ) + 1 := by
        have : 1 / (2 * t) ≤ 1 / t :=
          one_div_le_one_div_of_le ht0 (by linarith)
        exact this.trans h1t
      have hpsi1_nonneg : 0 ≤ Chebyshev.psi (1 / t) := Chebyshev.psi_nonneg _
      have hpsi2_nonneg : 0 ≤ Chebyshev.psi (1 / (2 * t)) := Chebyshev.psi_nonneg _
      have hpsi1_le : Chebyshev.psi (1 / t) ≤ Chebyshev.psi (((N + 2 : ℕ) : ℝ) + 1) :=
        Chebyshev.psi_mono h1t
      have hpsi2_le : Chebyshev.psi (1 / (2 * t)) ≤ Chebyshev.psi (((N + 2 : ℕ) : ℝ) + 1) :=
        Chebyshev.psi_mono h2t
      have hsq1 : (Chebyshev.psi (1 / t) - 1 / t) ^ 2 ≤
          (Chebyshev.psi (((N + 2 : ℕ) : ℝ) + 1) + (((N + 2 : ℕ) : ℝ) + 1)) ^ 2 := by
        nlinarith [ (by positivity : (0 : ℝ) ≤ 1 / t) ]
      have hsq2 : (Chebyshev.psi (1 / (2 * t)) - 1 / (2 * t)) ^ 2 ≤
          (Chebyshev.psi (((N + 2 : ℕ) : ℝ) + 1) + (((N + 2 : ℕ) : ℝ) + 1)) ^ 2 := by
        nlinarith [ (by positivity : (0 : ℝ) ≤ 1 / (2 * t)) ]
      rw [Real.norm_of_nonneg (by positivity)]
      linarith
  refine integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _) hInt
    (Eventually.of_forall fun t => ?_)
  dsimp only
  have h := dyadic_chebyshev_head_sq_le_centered_sq (1 / t)
  rwa [show (1 / t) / 2 = 1 / (2 * t) by ring] at h

end GaloisForLFunctions.BiScaleUncertainty

end
