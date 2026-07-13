import GaloisForLFunctions.RHTower.FiniteTransverseReflectionRigidity
import GaloisForLFunctions.RHTower.EvenPeriodicFlankRigidity

/-!
# Finite-transverse leaf-reflection rigidity: the analytic wrapper

An even entire function whose lower-flank trace is a finite sum of shift-eigenfunctions with
eigenvalues `ω^n` (`n` ranging over a finite set `S`, `ω` of infinite multiplicative order) and which
is bounded on the lower flank is constant.  The forward shift annihilator `∏_{n∈S}(R − ω^n)` kills
`G` on the lower flank; evenness turns the lower-flank decomposition into an upper-flank
decomposition into `ω^{−n}`-eigenfunctions, giving the reflected annihilator `∏_{n∈S}(R − ω^{−n})` on
the upper flank; the identity theorem promotes both to all of `ℂ`; the coprime-residual Bézout core
forces the exact period `R G = G`; and `even_periodic_flankBounded_const` closes the argument.
-/

open Polynomial Complex Filter Topology

noncomputable section

namespace RHTower

/-- Shift-by-`c` as a linear endomorphism of `ℂ → ℂ`. -/
def shiftEnd (c : ℂ) : Module.End ℂ (ℂ → ℂ) where
  toFun f := fun z => f (z + c)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem shiftEnd_apply (c : ℂ) (f : ℂ → ℂ) (z : ℂ) :
    shiftEnd c f z = f (z + c) := rfl

theorem shiftEnd_pow_apply (c : ℂ) (e : ℕ) (f : ℂ → ℂ) (z : ℂ) :
    ((shiftEnd c) ^ e) f z = f (z + e * c) := by
  induction e generalizing z with
  | zero => simp
  | succ e ih =>
    rw [pow_succ', Module.End.mul_apply, shiftEnd_apply, ih]
    congr 1; push_cast; ring

/-- Pointwise value of a polynomial evaluated at the shift operator. -/
theorem polyShiftOp_shiftEnd_apply (c : ℂ) (p : Polynomial ℂ) (f : ℂ → ℂ) (z : ℂ) :
    polyShiftOp (shiftEnd c) p f z =
      ∑ e ∈ p.support, p.coeff e * f (z + e * c) := by
  rw [polyShiftOp, Polynomial.eval₂_eq_sum, Polynomial.sum]
  simp only [LinearMap.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
    LinearMap.smul_apply, Pi.smul_apply, shiftEnd_pow_apply, smul_eq_mul]

/-- The full forward phase polynomial `∏_{n∈S}(X − ω^n)`. -/
def fullPhase (ω : ℂ) (s : Finset ℕ) : Polynomial ℂ :=
  ∏ n ∈ s, (Polynomial.X - Polynomial.C (ω ^ n))

/-- The full reflected phase polynomial `∏_{n∈S}(X − ω^{−n})`. -/
def fullPhaseInv (ω : ℂ) (s : Finset ℕ) : Polynomial ℂ :=
  ∏ n ∈ s, (Polynomial.X - Polynomial.C ((ω ^ n)⁻¹))

theorem fullPhase_eval_eq_zero {ω : ℂ} {s : Finset ℕ} {n : ℕ} (hn : n ∈ s) :
    (fullPhase ω s).eval (ω ^ n) = 0 := by
  rw [fullPhase, Polynomial.eval_prod]
  apply Finset.prod_eq_zero hn
  simp

theorem fullPhaseInv_eval_eq_zero {ω : ℂ} {s : Finset ℕ} {n : ℕ} (hn : n ∈ s) :
    (fullPhaseInv ω s).eval ((ω ^ n)⁻¹) = 0 := by
  rw [fullPhaseInv, Polynomial.eval_prod]
  apply Finset.prod_eq_zero hn
  simp

/-- Iterating a flank eigen-relation `g(z+c) = λ g(z)` (valid on a set closed under `+c`). -/
theorem eig_iter {g : ℂ → ℂ} {c lam : ℂ} {P : ℂ → Prop}
    (hclosed : ∀ z, P z → P (z + c))
    (heig : ∀ z, P z → g (z + c) = lam * g z)
    (e : ℕ) (z : ℂ) (hz : P z) : g (z + e * c) = lam ^ e * g z := by
  induction e generalizing z with
  | zero => simp
  | succ e ih =>
    have h1 : g (z + (e + 1 : ℕ) * c) = g ((z + c) + e * c) := by congr 1; push_cast; ring
    rw [h1, ih (z + c) (hclosed z hz), heig z hz]
    ring

/-- On a set `P` closed under `+ c`, if `G` is a finite sum of `λ n`-eigenfunctions there and `p`
vanishes at every `λ n`, then the operator `p` in the shift vanishes on `P`. -/
theorem polyShiftOp_eq_zero_on_of_eigenslice
    {G : ℂ → ℂ} {c : ℂ} {P : ℂ → Prop} {S : Finset ℕ} {Gn : ℕ → ℂ → ℂ} {lam : ℕ → ℂ}
    (p : Polynomial ℂ)
    (hclosed : ∀ z, P z → P (z + c))
    (hslice : ∀ z, P z → G z = ∑ n ∈ S, Gn n z)
    (heig : ∀ n ∈ S, ∀ z, P z → Gn n (z + c) = lam n * Gn n z)
    (hroot : ∀ n ∈ S, p.eval (lam n) = 0)
    {z : ℂ} (hz : P z) :
    polyShiftOp (shiftEnd c) p G z = 0 := by
  have hshift : ∀ e : ℕ, P (z + (e : ℂ) * c) := by
    intro e
    induction e with
    | zero => simpa using hz
    | succ e ih =>
      have := hclosed _ ih
      rwa [show z + (e : ℂ) * c + c = z + ((e + 1 : ℕ) : ℂ) * c by push_cast; ring] at this
  rw [polyShiftOp_shiftEnd_apply]
  calc ∑ e ∈ p.support, p.coeff e * G (z + e * c)
      = ∑ e ∈ p.support, ∑ n ∈ S, p.coeff e * Gn n (z + e * c) := by
        refine Finset.sum_congr rfl (fun e _ => ?_)
        rw [hslice _ (hshift e), Finset.mul_sum]
    _ = ∑ n ∈ S, ∑ e ∈ p.support, p.coeff e * ((lam n) ^ e * Gn n z) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun n hn => Finset.sum_congr rfl (fun e _ => ?_))
        rw [eig_iter hclosed (fun z' hz' => heig n hn z' hz') e z hz]
    _ = ∑ n ∈ S, p.eval (lam n) * Gn n z := by
        refine Finset.sum_congr rfl (fun n _ => ?_)
        have h1 : p.eval (lam n) = ∑ e ∈ p.support, p.coeff e * (lam n) ^ e := by
          rw [Polynomial.eval_eq_sum, Polynomial.sum]
        rw [h1, Finset.sum_mul]
        exact Finset.sum_congr rfl (fun e _ => by ring)
    _ = 0 := Finset.sum_eq_zero (fun n hn => by rw [hroot n hn, zero_mul])

/-- The polynomial-in-shift operator applied to a differentiable `G` is differentiable. -/
theorem differentiable_polyShiftOp_shiftEnd (c : ℂ) (p : Polynomial ℂ) {G : ℂ → ℂ}
    (hG : Differentiable ℂ G) :
    Differentiable ℂ (fun z => polyShiftOp (shiftEnd c) p G z) := by
  simp only [polyShiftOp_shiftEnd_apply]
  refine Differentiable.fun_sum (fun e _ => ?_)
  exact (hG.comp (differentiable_id.add_const _)).const_mul _

/-- Identity theorem: an entire polynomial-in-shift operator that vanishes on a neighbourhood of a
point vanishes everywhere. -/
theorem polyShiftOp_eq_zero_of_eventually {c : ℂ} (p : Polynomial ℂ) {G : ℂ → ℂ}
    (hG : Differentiable ℂ G) {z₀ : ℂ}
    (hev : (fun z => polyShiftOp (shiftEnd c) p G z) =ᶠ[𝓝 z₀] (0 : ℂ → ℂ)) :
    (polyShiftOp (shiftEnd c) p G : ℂ → ℂ) = 0 := by
  set F : ℂ → ℂ := fun z => polyShiftOp (shiftEnd c) p G z with hF
  have hFdiff : Differentiable ℂ F := differentiable_polyShiftOp_shiftEnd c p hG
  have hA1 : AnalyticOnNhd ℂ F Set.univ := hFdiff.differentiableOn.analyticOnNhd isOpen_univ
  have hA2 : AnalyticOnNhd ℂ (0 : ℂ → ℂ) Set.univ :=
    (differentiable_const (0 : ℂ)).differentiableOn.analyticOnNhd isOpen_univ
  have := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hA1 hA2 isPreconnected_univ
    (Set.mem_univ z₀) hev
  funext z
  exact this (Set.mem_univ z)


theorem fullPhase_eq_mul {ω : ℂ} {S : Finset ℕ} (h0 : 0 ∈ S) :
    fullPhase ω S = (Polynomial.X - 1) * forwardPhaseResidual ω S := by
  rw [fullPhase, forwardPhaseResidual, Finset.filter_ne',
    ← Finset.mul_prod_erase S (fun n => Polynomial.X - Polynomial.C (ω ^ n)) h0,
    pow_zero, Polynomial.C_1]

theorem fullPhase_eq {ω : ℂ} {S : Finset ℕ} (h0 : 0 ∉ S) :
    fullPhase ω S = forwardPhaseResidual ω S := by
  rw [fullPhase, forwardPhaseResidual, Finset.filter_true_of_mem (fun n hn => show n ≠ 0 from fun (h : n = 0) => h0 (h ▸ hn))]

theorem fullPhaseInv_eq_mul {ω : ℂ} {S : Finset ℕ} (h0 : 0 ∈ S) :
    fullPhaseInv ω S = (Polynomial.X - 1) * reflectedPhaseResidual ω S := by
  rw [fullPhaseInv, reflectedPhaseResidual, Finset.filter_ne',
    ← Finset.mul_prod_erase S (fun n => Polynomial.X - Polynomial.C ((ω ^ n)⁻¹)) h0,
    pow_zero, inv_one, Polynomial.C_1]

theorem fullPhaseInv_eq {ω : ℂ} {S : Finset ℕ} (h0 : 0 ∉ S) :
    fullPhaseInv ω S = reflectedPhaseResidual ω S := by
  rw [fullPhaseInv, reflectedPhaseResidual, Finset.filter_true_of_mem (fun n hn => show n ≠ 0 from fun (h : n = 0) => h0 (h ▸ hn))]

/-- **Finite-transverse leaf-reflection rigidity (analytic form).** An even entire `G` whose
lower-flank trace is a finite sum of shift eigenfunctions with eigenvalues `ω^n` (`ω` of infinite
multiplicative order, `n ∈ S`) and which is bounded on the lower flank is constant. -/
theorem finiteTransverse_reflection_rigidity
    {G : ℂ → ℂ} (hG : Differentiable ℂ G) (hEven : ∀ z, G (-z) = G z)
    {T w : ℝ} (hT : 0 < T) (hw : 0 < w)
    {ω : ℂ} (hω0 : ω ≠ 0) (hωinf : ∀ k : ℕ, 0 < k → ω ^ k ≠ 1)
    {S : Finset ℕ} {Gn : ℕ → ℂ → ℂ}
    (hslice : ∀ z, z.im ≤ -w → G z = ∑ n ∈ S, Gn n z)
    (heig : ∀ n ∈ S, ∀ z, z.im ≤ -w → Gn n (z + (T : ℂ)) = ω ^ n * Gn n z)
    {B : ℝ} (hbound : ∀ z, z.im ≤ -w → ‖G z‖ ≤ B) :
    ∀ s t : ℂ, G s = G t := by
  have hlowClosed : ∀ z' : ℂ, z'.im ≤ -w → (z' + (T : ℂ)).im ≤ -w :=
    fun z' hz' => by rw [Complex.add_im, Complex.ofReal_im, add_zero]; exact hz'
  have hlowOpen : IsOpen {z : ℂ | z.im < -w} := isOpen_lt Complex.continuous_im continuous_const
  -- forward annihilator, globalized by the identity theorem
  have hfwd : (polyShiftOp (shiftEnd (T : ℂ)) (fullPhase ω S) G : ℂ → ℂ) = 0 := by
    refine polyShiftOp_eq_zero_of_eventually (fullPhase ω S) hG (z₀ := ⟨0, -(w + 1)⟩) ?_
    filter_upwards [hlowOpen.mem_nhds (show (⟨0, -(w + 1)⟩ : ℂ).im < -w by
      show -(w + 1) < -w; linarith)] with z hz
    simp only [Pi.zero_apply]
    exact polyShiftOp_eq_zero_on_of_eigenslice (fullPhase ω S) hlowClosed hslice heig
      (fun n hn => fullPhase_eval_eq_zero hn) (le_of_lt hz)
  -- upper-flank eigen-decomposition via evenness, then reflected annihilator
  have huppClosed : ∀ z' : ℂ, w ≤ z'.im → w ≤ (z' + (T : ℂ)).im :=
    fun z' hz' => by rw [Complex.add_im, Complex.ofReal_im, add_zero]; exact hz'
  have hsliceU : ∀ z, w ≤ z.im → G z = ∑ n ∈ S, Gn n (-z) := by
    intro z hz
    rw [← hEven z, hslice (-z) (by rw [Complex.neg_im]; linarith)]
  have heigU : ∀ n ∈ S, ∀ z, w ≤ z.im → Gn n (-(z + (T : ℂ))) = (ω ^ n)⁻¹ * Gn n (-z) := by
    intro n hn z hz
    have hu : (-z - (T : ℂ)).im ≤ -w := by
      rw [Complex.sub_im, Complex.neg_im, Complex.ofReal_im, sub_zero]; linarith
    have hkey := heig n hn (-z - (T : ℂ)) hu
    rw [show -z - (T : ℂ) + (T : ℂ) = -z by ring] at hkey
    have hωn0 : ω ^ n ≠ 0 := pow_ne_zero n hω0
    rw [show -(z + (T : ℂ)) = -z - (T : ℂ) by ring, hkey, ← mul_assoc,
      inv_mul_cancel₀ hωn0, one_mul]
  have hrev : (polyShiftOp (shiftEnd (T : ℂ)) (fullPhaseInv ω S) G : ℂ → ℂ) = 0 := by
    refine polyShiftOp_eq_zero_of_eventually (fullPhaseInv ω S) hG (z₀ := ⟨0, w + 1⟩) ?_
    have huppOpen : IsOpen {z : ℂ | w < z.im} := isOpen_lt continuous_const Complex.continuous_im
    filter_upwards [huppOpen.mem_nhds (show w < (⟨0, w + 1⟩ : ℂ).im by
      show w < w + 1; linarith)] with z hz
    simp only [Pi.zero_apply]
    exact polyShiftOp_eq_zero_on_of_eigenslice (fullPhaseInv ω S) huppClosed hsliceU heigU
      (fun n hn => fullPhaseInv_eval_eq_zero hn) (le_of_lt hz)
  -- Bézout: coprime residuals force the period, then Liouville
  by_cases h0 : 0 ∈ S
  · rw [fullPhase_eq_mul h0] at hfwd
    rw [fullPhaseInv_eq_mul h0] at hrev
    have hfix : shiftEnd (T : ℂ) G = G :=
      fixed_of_coprime_reflected_shift_annihilators
        (forward_reflected_phase_residual_isCoprime hω0 hωinf S) hfwd hrev
    have hper : Function.Periodic G (T : ℂ) := by
      intro z; have := congrFun hfix z; rwa [shiftEnd_apply] at this
    exact even_periodic_flankBounded_const hT hw hG (fun z => (hEven z).symm) hper hbound
  · rw [fullPhase_eq h0] at hfwd
    rw [fullPhaseInv_eq h0] at hrev
    have hG0 : (G : ℂ → ℂ) = 0 :=
      eq_zero_of_coprime_polyShiftOp
        (forward_reflected_phase_residual_isCoprime hω0 hωinf S) hfwd hrev
    intro s t; simp only [hG0, Pi.zero_apply]

end RHTower
