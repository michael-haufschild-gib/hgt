import GaloisForLFunctions.RHTower.DeningerCollarExchange
import GaloisForLFunctions.HTGeometry.FlowTemperedGrowth

/-!
# Modulation of the exponentially decreasing source

Multiplying a source cochain by the unimodular character `e^{2πict}` keeps it in the source: the
character and all of its derivatives are bounded, so the Leibniz estimate costs no exponential
weight at all.  On the Fourier side modulation is translation, which is what makes the source rich
enough to separate the points of the arithmetic frequency lattice.

* `deningerModulationWeight` : the character `e^{2πict}`.
* `deningerModulationWeight_norm_iteratedFDeriv` : its derivatives have norm `(2π|c|)^n`.
* `deningerModulate` : **modulation as an operation of the source.**
-/

namespace RHTower

open SchwartzMap
open GaloisForLFunctions.HTGeometry
open scoped ContDiff

noncomputable section

/-- The unimodular modulation weight `e^{2πict}`. -/
def deningerModulationWeight (c : ℝ) : ℝ → ℂ :=
  cexpLin (2 * (Real.pi : ℂ) * Complex.I * (c : ℂ))

theorem deningerModulationWeight_apply (c t : ℝ) :
    deningerModulationWeight c t
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (c : ℂ) * (t : ℂ)) := rfl

theorem deningerModulationWeight_contDiff (c : ℝ) :
    ContDiff ℝ ∞ (deningerModulationWeight c) :=
  Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)

theorem deningerModulationWeight_norm (c t : ℝ) : ‖deningerModulationWeight c t‖ = 1 := by
  rw [deningerModulationWeight_apply, Complex.norm_exp]
  norm_num [Complex.ext_iff, Complex.mul_re, Complex.mul_im]

/-- **Every derivative of the modulation weight has norm `(2π|c|)^n`.** -/
theorem deningerModulationWeight_norm_iteratedFDeriv (c : ℝ) (n : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ n (deningerModulationWeight c) x‖ = (2 * Real.pi * |c|) ^ n := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, deningerModulationWeight,
    congrFun (iteratedDeriv_cexpLin (2 * (Real.pi : ℂ) * Complex.I * (c : ℂ)) n) x,
    norm_mul, norm_pow]
  have hw : ‖2 * (Real.pi : ℂ) * Complex.I * (c : ℂ)‖ = 2 * Real.pi * |c| := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hval : ‖cexpLin (2 * (Real.pi : ℂ) * Complex.I * (c : ℂ)) x‖ = 1 :=
    deningerModulationWeight_norm c x
  rw [hw, hval, mul_one]

/-- The pointwise product `e^{2πict} h(t)`. -/
def deningerModulateFun (c : ℝ) (h : 𝓢(ℝ, ℂ)) (t : ℝ) : ℂ :=
  deningerModulationWeight c t * h t

theorem deningerModulateFun_contDiff (c : ℝ) (h : 𝓢(ℝ, ℂ)) :
    ContDiff ℝ ∞ (deningerModulateFun c h) :=
  (deningerModulationWeight_contDiff c).mul h.smooth'

/-- **Modulation keeps the source**, at no cost in exponential weight. -/
theorem deningerModulateFun_bounds {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerExpSchwartz) (c : ℝ) :
    ∀ (A : ℝ) (n : ℕ), ∃ C : ℝ, ∀ x : ℝ,
      Real.exp (A * |x|) * ‖iteratedFDeriv ℝ n (deningerModulateFun c h) x‖ ≤ C := by
  intro A n
  choose C hC using fun m : ℕ => hh A m
  refine ⟨∑ i ∈ Finset.range (n + 1),
    (n.choose i : ℝ) * ((2 * Real.pi * |c|) ^ i * max (C (n - i)) 0), fun x => ?_⟩
  have hleib := norm_iteratedFDeriv_mul_le (f := deningerModulationWeight c)
    (g := (h : ℝ → ℂ)) (deningerModulationWeight_contDiff c) h.smooth' x
    (n := n) ENat.LEInfty.out
  have hexp : (0 : ℝ) < Real.exp (A * |x|) := Real.exp_pos _
  refine le_trans (mul_le_mul_of_nonneg_left hleib hexp.le) ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [deningerModulationWeight_norm_iteratedFDeriv]
  have hbase : Real.exp (A * |x|) * ‖iteratedFDeriv ℝ (n - i) (h : ℝ → ℂ) x‖
      ≤ max (C (n - i)) 0 := le_trans (hC (n - i) x) (le_max_left _ _)
  calc Real.exp (A * |x|) * ((n.choose i : ℝ) * (2 * Real.pi * |c|) ^ i
        * ‖iteratedFDeriv ℝ (n - i) (h : ℝ → ℂ) x‖)
      = (n.choose i : ℝ) * (2 * Real.pi * |c|) ^ i
        * (Real.exp (A * |x|) * ‖iteratedFDeriv ℝ (n - i) (h : ℝ → ℂ) x‖) := by ring
    _ ≤ (n.choose i : ℝ) * (2 * Real.pi * |c|) ^ i * max (C (n - i)) 0 := by
        have hnn : (0 : ℝ) ≤ (n.choose i : ℝ) * (2 * Real.pi * |c|) ^ i := by positivity
        exact mul_le_mul_of_nonneg_left hbase hnn
    _ = (n.choose i : ℝ) * ((2 * Real.pi * |c|) ^ i * max (C (n - i)) 0) := by ring

/-- **Modulation as an operation of the source.** -/
def deningerModulate (c : ℝ) (h : DeningerExpSchwartz) : DeningerExpSchwartz :=
  ⟨deningerExpSchwartzOfBounds
      (deningerModulateFun c ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)))
      (deningerModulateFun_contDiff c _) (deningerModulateFun_bounds h.2 c),
    deningerExpSchwartzOfBounds_mem _ _ _⟩

@[simp]
theorem deningerModulate_apply (c : ℝ) (h : DeningerExpSchwartz) (t : ℝ) :
    ((deningerModulate c h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (c : ℂ) * (t : ℂ))
        * ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t := rfl

end

end RHTower
