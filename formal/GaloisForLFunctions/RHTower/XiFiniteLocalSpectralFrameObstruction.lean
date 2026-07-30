import GaloisForLFunctions.RHTower.CompletedFluxGermRigidity
import GaloisForLFunctions.RHTower.LambertRayRecovery
import GaloisForLFunctions.RHTower.FiniteHermiteCRT
import GaloisForLFunctions.RHTower.XiZerosInfinite

/-!
# Entire spectral densities cannot orient the horizontal Xi derivative

A finite family of constant-coefficient differential filters has polynomial Fourier symbols.
If its autocorrelation energies represented the horizontal derivative of the completed Xi
modulus on one positive-aperture line, the logarithmic derivative of `xi` would satisfy a
polynomial finite-difference equation.  The residue-filled completed-flux germ then propagates
every Xi zero by the corresponding nonzero real shift, with multiplicity and without assuming
simplicity.  Iteration exits the critical strip, a contradiction.

The result is an unconditional carrier necessity law.  A positive orientation of the Hedenmalm
center-mixed current cannot be supplied by any entire spectral density, hence not by a finite
constant-coefficient local frame.  A successful factorization must carry a non-entire transverse
divisor singularity through a nonlocal, cofinally arithmetic, or infinite-dimensional carrier.
-/

open Complex Set Metric Filter Topology Polynomial

namespace RHTower

noncomputable section

/-- An entire coboundary law for the completed Xi logarithmic flux under a real shift. -/
def XiEntireFluxCoboundary (h : ℝ) (E : ℂ → ℂ) : Prop :=
  Differentiable ℂ E ∧
    ∀ z : ℂ, xi z ≠ 0 → xi (z - (h : ℂ)) ≠ 0 →
      seamFluxCochain z - seamFluxCochain (z - (h : ℂ)) = E z

/-- A polynomial coboundary law for the completed Xi logarithmic flux under a real shift. -/
def XiPolynomialFluxCoboundary (h : ℝ) (P : Polynomial ℂ) : Prop :=
  ∀ z : ℂ, xi z ≠ 0 → xi (z - (h : ℂ)) ≠ 0 →
    seamFluxCochain z - seamFluxCochain (z - (h : ℂ)) = P.eval z

/-- An entire multiplicative law for the horizontal derivative of the completed Xi modulus on one
vertical line. -/
def XiEntireHermitianDiagonalLaw (a : ℝ) (Q : ℂ → ℂ) : Prop :=
  Differentiable ℂ Q ∧
    ∀ b : ℝ,
      deriv xi ((1 : ℂ) / 2 + (a : ℂ) + (b : ℂ) * I) *
            xi ((1 : ℂ) / 2 + (a : ℂ) - (b : ℂ) * I) +
          xi ((1 : ℂ) / 2 + (a : ℂ) + (b : ℂ) * I) *
            deriv xi ((1 : ℂ) / 2 + (a : ℂ) - (b : ℂ) * I) =
        Q (b : ℂ) *
          xi ((1 : ℂ) / 2 + (a : ℂ) + (b : ℂ) * I) *
            xi ((1 : ℂ) / 2 + (a : ℂ) - (b : ℂ) * I)

/-- A polynomial multiplicative law for the horizontal derivative of the completed Xi modulus on
one vertical line.  A finite constant-coefficient differential autocorrelation frame produces a
law of this form. -/
def XiPolynomialHermitianDiagonalLaw (a : ℝ) (Q : Polynomial ℂ) : Prop :=
  ∀ b : ℝ,
    deriv xi ((1 : ℂ) / 2 + (a : ℂ) + (b : ℂ) * I) *
          xi ((1 : ℂ) / 2 + (a : ℂ) - (b : ℂ) * I) +
        xi ((1 : ℂ) / 2 + (a : ℂ) + (b : ℂ) * I) *
          deriv xi ((1 : ℂ) / 2 + (a : ℂ) - (b : ℂ) * I) =
      Q.eval (b : ℂ) *
        xi ((1 : ℂ) / 2 + (a : ℂ) + (b : ℂ) * I) *
          xi ((1 : ℂ) / 2 + (a : ℂ) - (b : ℂ) * I)

/-- Polynomial symbol of the spectral energy `|p(i b)|²` on the real frequency axis. -/
def polynomialSpectralSquare (p : Polynomial ℂ) : Polynomial ℂ :=
  let pI := p.comp (Polynomial.C I * Polynomial.X)
  pI * polynomialConj pI

/-- Evaluation of `polynomialSpectralSquare` is the expected nonnegative modulus square on real
frequency. -/
theorem polynomialSpectralSquare_eval_real (p : Polynomial ℂ) (b : ℝ) :
    (polynomialSpectralSquare p).eval (b : ℂ) =
      p.eval ((b : ℂ) * I) * (starRingEnd ℂ) (p.eval ((b : ℂ) * I)) := by
  rw [polynomialSpectralSquare, Polynomial.eval_mul, eval_polynomialConj,
    Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  simp only [Complex.conj_ofReal]
  rw [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  rw [mul_comm I (b : ℂ)]

/-- A finite constant-coefficient polynomial spectral frame for the horizontal Xi derivative.
Each frame symbol contributes the nonnegative real-axis density `|p_j(i b)|²`. -/
def XiFiniteLocalPolynomialSpectralFrame (a : ℝ) : Prop :=
  ∃ (n : ℕ) (p : Fin n → Polynomial ℂ),
    XiPolynomialHermitianDiagonalLaw a
      (∑ j : Fin n, polynomialSpectralSquare (p j))

/-- An entire flux coboundary propagates every Xi zero by its shift.  The proof uses the
residue-filled flux germ, so no simplicity assumption is needed. -/
theorem xi_zero_shift_of_entireFluxCoboundary
    {h : ℝ} {E : ℂ → ℂ} (hrel : XiEntireFluxCoboundary h E)
    {ρ : ℂ} (hzero : xi ρ = 0) :
    xi (ρ - (h : ℂ)) = 0 := by
  by_contra hshift
  have hshiftAn : AnalyticAt ℂ seamFluxCochain (ρ - (h : ℂ)) := by
    have hxi : AnalyticAt ℂ xi (ρ - (h : ℂ)) :=
      xi_analyticOnNhd_univ _ (Set.mem_univ _)
    change AnalyticAt ℂ (fun z => -logDeriv xi z) (ρ - (h : ℂ))
    exact (hxi.deriv.div hxi hshift).neg
  have hshiftComp : AnalyticAt ℂ
      (fun x : ℂ => seamFluxCochain ((ρ + x) - (h : ℂ))) 0 := by
    apply AnalyticAt.comp_of_eq hshiftAn
    · fun_prop
    · ring
  have hE : AnalyticAt ℂ (fun x : ℂ => E (ρ + x)) 0 := by
    have hd : Differentiable ℂ (fun x : ℂ => E (ρ + x)) :=
      hrel.1.comp ((differentiable_const ρ).add differentiable_id)
    exact (hd.differentiableOn.analyticOnNhd isOpen_univ) 0 (Set.mem_univ 0)
  have hrhs : AnalyticAt ℂ
      (fun x : ℂ => x *
        (E (ρ + x) + seamFluxCochain ((ρ + x) - (h : ℂ)))) 0 :=
    analyticAt_id.mul (hE.add hshiftComp)
  obtain ⟨R, hR, q, _hqAn, hq0, hfac⟩ := xi_peel_ball ρ
  have hnearZero : ∀ᶠ x : ℂ in 𝓝[≠] 0, ρ + x ∈ ball ρ R := by
    have hc : ContinuousAt (fun x : ℂ => ρ + x) 0 := by fun_prop
    have ht : Tendsto (fun x : ℂ => ρ + x) (𝓝 0) (𝓝 ρ) := by simpa using hc.tendsto
    have hev := ht (isOpen_ball.mem_nhds (mem_ball_self hR))
    have hev' : ∀ᶠ x : ℂ in 𝓝 0, ρ + x ∈ ball ρ R := by exact hev
    exact hev'.filter_mono nhdsWithin_le_nhds
  have hshiftNear : ∀ᶠ x : ℂ in 𝓝 0, xi ((ρ + x) - (h : ℂ)) ≠ 0 := by
    have hc : ContinuousAt (fun x : ℂ => xi ((ρ + x) - (h : ℂ))) 0 := by
      have hinner : ContinuousAt (fun x : ℂ => (ρ + x) - (h : ℂ)) 0 := by fun_prop
      have hcomp := (xi_analyticOnNhd_univ _ (Set.mem_univ _)).continuousAt.comp hinner
      simpa [Function.comp_def] using hcomp
    exact hc.eventually_ne (by simpa using hshift)
  have hnear : completedFluxGermAt ρ =ᶠ[𝓝[≠] 0]
      fun x : ℂ => x *
        (E (ρ + x) + seamFluxCochain ((ρ + x) - (h : ℂ))) := by
    filter_upwards [hnearZero, hshiftNear.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with x hxball hxshift hxmem
    have hx0 : x ≠ 0 := by simpa using hxmem
    have hxi : xi (ρ + x) ≠ 0 := by
      rw [hfac (ρ + x) hxball]
      exact mul_ne_zero (pow_ne_zero _ (by simpa using hx0)) (hq0 (ρ + x) hxball)
    rw [completedFluxGermAt, if_neg hx0]
    have hflux := hrel.2 (ρ + x) hxi hxshift
    have hflux' : seamFluxCochain (ρ + x) =
        E (ρ + x) + seamFluxCochain ((ρ + x) - (h : ℂ)) := by
      linear_combination hflux
    rw [hflux']
  have heq : completedFluxGermAt ρ =ᶠ[𝓝 0]
      fun x : ℂ => x *
        (E (ρ + x) + seamFluxCochain ((ρ + x) - (h : ℂ))) :=
    ((completedFluxGermAt_analyticAt_zero ρ).frequently_eq_iff_eventually_eq hrhs).mp
      hnear.frequently
  have hval := heq.eq_of_nhds
  simp only [completedFluxGermAt_zero, zero_mul] at hval
  have hord : (analyticOrderAt xi ρ).toNat = 0 := by
    exact_mod_cast neg_eq_zero.mp hval
  exact (xi_order_toNat_ne_zero hzero) hord

/-- A polynomial flux coboundary propagates every Xi zero by its shift. -/
theorem xi_zero_shift_of_polynomialFluxCoboundary
    {h : ℝ} {P : Polynomial ℂ} (hrel : XiPolynomialFluxCoboundary h P)
    {ρ : ℂ} (hzero : xi ρ = 0) :
    xi (ρ - (h : ℂ)) = 0 := by
  exact xi_zero_shift_of_entireFluxCoboundary
    ⟨P.differentiable, hrel⟩ hzero

/-- The completed Xi logarithmic flux has no entire coboundary under a positive real shift. -/
theorem no_XiEntireFluxCoboundary_of_pos {h : ℝ} (hh : 0 < h) :
    ¬ ∃ E : ℂ → ℂ, XiEntireFluxCoboundary h E := by
  rintro ⟨E, hrel⟩
  obtain ⟨ρ0, hρmem⟩ := xiDivisorSupport_infinite.nonempty
  let q0 : XiDivisorSupport := ⟨ρ0, hρmem⟩
  let ρ : ℂ := q0
  have hρzero : xi ρ = 0 := xi_eq_zero_of_mem_divisor_support q0
  have hzeros : ∀ n : ℕ, xi (ρ - ((n : ℝ) * h : ℂ)) = 0 := by
    intro n
    induction n with
    | zero => simpa using hρzero
    | succ n ih =>
        have hnext := xi_zero_shift_of_entireFluxCoboundary hrel ih
        have harg : ρ - (((n + 1 : ℕ) : ℝ) * h : ℂ) =
            (ρ - ((n : ℝ) * h : ℂ)) - (h : ℂ) := by
          push_cast
          ring
        rw [harg]
        exact hnext
  obtain ⟨n : ℕ, hn⟩ := exists_nat_gt (ρ.re / h)
  have hmul : ρ.re < (n : ℝ) * h := (div_lt_iff₀ hh).mp hn
  let z : ℂ := ρ - ((n : ℝ) * h : ℂ)
  have hz0 : xi z = 0 := hzeros n
  let q : XiDivisorSupport := ⟨z, mem_xi_divisor_support_of_eq_zero hz0⟩
  have hpos := (xi_divisor_support_re_mem_open_unit q).1
  change 0 < z.re at hpos
  dsimp [z] at hpos
  simp [Complex.mul_re] at hpos
  linarith

/-- The completed Xi logarithmic flux has no polynomial coboundary under a positive real shift. -/
theorem no_XiPolynomialFluxCoboundary_of_pos {h : ℝ} (hh : 0 < h) :
    ¬ ∃ P : Polynomial ℂ, XiPolynomialFluxCoboundary h P := by
  rintro ⟨P, hrel⟩
  exact no_XiEntireFluxCoboundary_of_pos hh
    ⟨fun z => P.eval z, P.differentiable, hrel⟩

/-- **Explicit flux coboundary from an entire Hermitian diagonal law.**  The diagonal law forces the
Wronskian-type combination to vanish identically, and the resulting logarithmic-derivative identity
exhibits the seam flux as the coboundary of the explicit function `z ↦ -Q(-i(z - 1/2 - a))`. -/
theorem entireFluxCoboundary_of_entireHermitianDiagonalLaw_explicit
    {a : ℝ} {Q : ℂ → ℂ} (hlaw : XiEntireHermitianDiagonalLaw a Q) :
    XiEntireFluxCoboundary (2 * a)
      (fun z => -Q (-I * (z - ((1 : ℂ) / 2 + (a : ℂ))))) := by

  let c : ℂ := (1 : ℂ) / 2 + (a : ℂ)
  let H : ℂ → ℂ := fun b =>
    deriv xi (c + b * I) * xi (c - b * I) +
      xi (c + b * I) * deriv xi (c - b * I) -
        Q b * xi (c + b * I) * xi (c - b * I)
  have hderivXi : Differentiable ℂ (deriv xi) :=
    analyticOnNhd_univ_iff_differentiable.mp xi_analyticOnNhd_univ.deriv
  have hplus : Differentiable ℂ (fun b : ℂ => c + b * I) := by fun_prop
  have hminus : Differentiable ℂ (fun b : ℂ => c - b * I) := by fun_prop
  have hHdiff : Differentiable ℂ H := by
    dsimp only [H]
    have hxiPlus : Differentiable ℂ (fun b : ℂ => xi (c + b * I)) :=
      xi_differentiable.comp hplus
    have hxiMinus : Differentiable ℂ (fun b : ℂ => xi (c - b * I)) :=
      xi_differentiable.comp hminus
    have hdPlus : Differentiable ℂ (fun b : ℂ => deriv xi (c + b * I)) :=
      hderivXi.comp hplus
    have hdMinus : Differentiable ℂ (fun b : ℂ => deriv xi (c - b * I)) :=
      hderivXi.comp hminus
    exact (hdPlus.mul hxiMinus).add (hxiPlus.mul hdMinus) |>.sub
      ((hlaw.1.mul hxiPlus).mul hxiMinus)
  have hHan : AnalyticOnNhd ℂ H Set.univ :=
    analyticOnNhd_univ_iff_differentiable.mpr hHdiff
  have hHreal : ∀ b : ℝ, H (b : ℂ) = 0 := by
    intro b
    have hb := hlaw.2 b
    dsimp only [H, c]
    linear_combination hb
  have hHzero : ∀ b : ℂ, H b = 0 :=
    entire_eq_zero_of_zero_on_real_tail H 0 hHan (fun x _hx => hHreal x)
  let E : ℂ → ℂ := fun z => -Q (-I * (z - c))
  refine ⟨?_, ?_⟩
  · have hinner : Differentiable ℂ (fun z : ℂ => -I * (z - c)) := by fun_prop
    exact (hlaw.1.comp hinner).neg
  · intro z hz hzshift
    let b : ℂ := -I * (z - c)
    have hbplus : c + b * I = z := by
      dsimp only [b]
      calc
        c + -I * (z - c) * I = c + ((-I) * I) * (z - c) := by ring
        _ = z := by rw [show (-I) * I = (1 : ℂ) by rw [neg_mul, I_mul_I]; ring]; ring
    have hbminus : c - b * I = 1 - (z - ((2 * a : ℝ) : ℂ)) := by
      dsimp only [b, c]
      push_cast
      calc
        1 / 2 + (a : ℂ) - (-I * (z - (1 / 2 + (a : ℂ)))) * I =
            1 / 2 + (a : ℂ) - ((-I) * I) * (z - (1 / 2 + (a : ℂ))) := by ring
        _ = 1 - (z - 2 * (a : ℂ)) := by
          rw [show (-I) * I = (1 : ℂ) by rw [neg_mul, I_mul_I]; ring]
          ring
    have htne : xi (c - b * I) ≠ 0 := by
      rw [hbminus, xi_one_sub]
      exact hzshift
    have hHb := hHzero b
    have hlog : logDeriv xi z + logDeriv xi (c - b * I) = Q b := by
      rw [logDeriv_apply, logDeriv_apply, ← hbplus]
      dsimp only [H] at hHb
      have hzplus : xi (c + b * I) ≠ 0 := by simpa [hbplus] using hz
      calc
        deriv xi (c + b * I) / xi (c + b * I) +
            deriv xi (c - b * I) / xi (c - b * I) =
            (deriv xi (c + b * I) * xi (c - b * I) +
              xi (c + b * I) * deriv xi (c - b * I)) /
                (xi (c + b * I) * xi (c - b * I)) := by
              field_simp [hzplus, htne]
        _ = Q b := by
          apply (div_eq_iff (mul_ne_zero hzplus htne)).2
          linear_combination hHb
    have hlog' : logDeriv xi z -
        logDeriv xi (z - (((2 * a : ℝ)) : ℂ)) = Q b := by
      rw [hbminus, logDeriv_xi_reciprocity] at hlog
      exact hlog
    change -logDeriv xi z - -logDeriv xi (z - (((2 * a : ℝ)) : ℂ)) = E z
    have hEval : E z = -Q b := by rfl
    rw [hEval]
    linear_combination -hlog'

/-- An entire Hermitian-diagonal law analytically continues to an entire coboundary for the
completed logarithmic flux under the transverse shift `2a`. -/
theorem entireFluxCoboundary_of_entireHermitianDiagonalLaw
    {a : ℝ} {Q : ℂ → ℂ} (hlaw : XiEntireHermitianDiagonalLaw a Q) :
    ∃ E : ℂ → ℂ, XiEntireFluxCoboundary (2 * a) E :=
  ⟨_, entireFluxCoboundary_of_entireHermitianDiagonalLaw_explicit hlaw⟩

/-- No positive aperture admits an entire Hermitian-diagonal multiplier law. -/
theorem no_XiEntireHermitianDiagonalLaw_of_pos {a : ℝ} (ha : 0 < a) :
    ¬ ∃ Q : ℂ → ℂ, XiEntireHermitianDiagonalLaw a Q := by
  rintro ⟨Q, hQ⟩
  obtain ⟨E, hE⟩ := entireFluxCoboundary_of_entireHermitianDiagonalLaw hQ
  exact no_XiEntireFluxCoboundary_of_pos (by linarith : 0 < 2 * a) ⟨E, hE⟩

/-- A polynomial Hermitian-diagonal law analytically continues to a polynomial coboundary for the
completed logarithmic flux under the transverse shift `2a`. -/
theorem polynomialFluxCoboundary_of_hermitianDiagonalLaw
    {a : ℝ} {Q : Polynomial ℂ} (hlaw : XiPolynomialHermitianDiagonalLaw a Q) :
    ∃ P : Polynomial ℂ, XiPolynomialFluxCoboundary (2 * a) P := by
  refine ⟨-(Q.comp (Polynomial.C (-I) *
    (Polynomial.X - Polynomial.C ((1 : ℂ) / 2 + (a : ℂ))))), ?_⟩
  intro z hz hzshift
  have h := (entireFluxCoboundary_of_entireHermitianDiagonalLaw_explicit
    (Q := fun w => Q.eval w) ⟨Q.differentiable, hlaw⟩).2 z hz hzshift
  rw [h, Polynomial.eval_neg, Polynomial.eval_comp, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]

/-- No positive critical aperture admits a polynomial Hermitian-diagonal law. -/
theorem no_XiPolynomialHermitianDiagonalLaw_of_pos {a : ℝ} (ha : 0 < a) :
    ¬ ∃ Q : Polynomial ℂ, XiPolynomialHermitianDiagonalLaw a Q := by
  rintro ⟨Q, hQ⟩
  obtain ⟨P, hP⟩ := polynomialFluxCoboundary_of_hermitianDiagonalLaw hQ
  exact no_XiPolynomialFluxCoboundary_of_pos (by linarith : 0 < 2 * a) ⟨P, hP⟩

/-- **Finite local spectral-frame obstruction.** At every positive aperture, the horizontal Xi
derivative admits no finite Gram density assembled from constant-coefficient polynomial symbols. -/
theorem not_XiFiniteLocalPolynomialSpectralFrame_of_pos {a : ℝ} (ha : 0 < a) :
    ¬ XiFiniteLocalPolynomialSpectralFrame a := by
  rintro ⟨n, p, hframe⟩
  exact no_XiPolynomialHermitianDiagonalLaw_of_pos ha ⟨_, hframe⟩

end

end RHTower
